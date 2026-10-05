import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Bignum.X86_64.Valid

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PdCode`. -/
section

/-!
# `vg_rsa_public_precomputed` on x86-64: correctness

The entry (`pdEntry_ok`); the values of a valid modulus in `pre` pass the
checks (`checks_true`), and values that pass them make `rest` compute
(`checks_facts`); the whole function (`pdCode_correct`), against
`pdContract`, which states the shared contract's precondition on the
registers and the stack.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

variable {M : Mont}

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_public_precomputed(out = rdi, out_len = rsi, pre = rdx,
pre_len = rcx, e = r8, e_len = r9, input = [rsp + 8], input_len = [rsp + 16],
scratch = [rsp + 24], scratch_len = [rsp + 32])`. -/
def pdContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let pre : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let inp : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
      s.rd = [pre, e, inp, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint pre ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      pre.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint pre ∧ ret.Disjoint e ∧ ret.Disjoint inp ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rsi).toNat ∧ (s.gpr .rcx).toNat = Spec.Rsa.precomputedWords (s.gpr .rsi).toNat ∧
      (stackArg s 1).toNat = (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧
      (s.gpr .r9).toNat ≤ (s.gpr .rsi).toNat ∧ Spec.Rsa.scratchWords (s.gpr .rsi).toNat ≤ (stackArg s 3).toNat
  post s s' :=
    ∀ nB : List Byte, nB.length = (s.gpr .rsi).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((s'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOp nB (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧
      Spec.Rsa.wordsAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.wordsAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

/-! ## The entry -/

theorem pdEntry_eq : Precomputed.entry = ([.mov .r11 (.mem { base := .rsp, disp := 24 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sOut) .rdi, .store (hdr11 sN) .rdx, .store (hdr11 sK) .rsi, .store (hdr11 sE) .r8,
    .store (hdr11 sElen) .r9] : List Instr) ++ [.mov .rax (.mem { base := .rsp, disp := 8 }), .store (hdr11 sIn) .rax,
    .mov .rdi (.reg .r11)] := rfl

/-- `entry`: the header, from the arguments (`out_len` for `k`), and the
working space's base (the third stack argument) in `rdi`. -/
theorem pdEntry_ok {s : State} {B : Addr} (hB : stackArg s 2 = B)
    (hw : ∀ i < 22, InRegions s.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8)
    (ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) (ha2 : InRegions (s.rd ++ s.wr) (stackArgAddr s 2) 8)
    (hsep : ∀ m', VG.Proof.Bignum.X86_64.Outside B 0 (8 * 22) s.mem m' → m'.readW (stackArgAddr s 0) 64 = stackArg s 0) :
    WP isa (.block Precomputed.entry) s fun t => t.gpr .rdi = B ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 0) = s.gpr .rbx ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 1) = s.gpr .rbp ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 2) = s.gpr .r12 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 3) = s.gpr .r13 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 4) = s.gpr .r14 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 5) = s.gpr .r15 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sOut) = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sN) = s.gpr .rdx ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sK) = s.gpr .rsi ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sE) = s.gpr .r8 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sElen) = s.gpr .r9 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sIn) = stackArg s 0 ∧
      VG.Proof.Bignum.X86_64.Outside B 0 (8 * 22) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r11, .rax, .rdi] s t := by
  have e0 : s.gpr .rsp + BitVec.ofInt 64 8 = stackArgAddr s 0 := rfl
  have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
  have hB' : s.mem.readW (stackArgAddr s 2) 64 = B := hB
  have hA0 : s.mem.readW (stackArgAddr s 0) 64 = stackArg s 0 := rfl
  rw [VG.Proof.Bignum.X86_64.pdEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 0) = s.gpr .rbx ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 1) = s.gpr .rbp ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 2) = s.gpr .r12 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 3) = s.gpr .r13 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 4) = s.gpr .r14 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 5) = s.gpr .r15 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sOut) = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sN) = s.gpr .rdx ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sK) = s.gpr .rsi ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sE) = s.gpr .r8 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sElen) = s.gpr .r9 ∧ VG.Proof.Bignum.X86_64.Outside B 0 (8 * 22) s.mem t.mem) ?_ rfl)
    fun t₁ ⟨⟨h11, h0, h1, h2, h3, h4, h5, hO, hN, hK, hE, hL, ho₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e2, ha2, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sOut (by decide),
      hw sN (by decide), hw sK (by decide), hw sE (by decide), hw sElen (by decide)]
    exact entryMem_facts _ _ _ _ _ _ _ _ _ _ _ _ _
  have hr₁ : t₁.mem.readW (stackArgAddr s 0) 64 = stackArg s 0 := hsep _ ho₁
  have ha0₁ : InRegions (t₁.rd ++ t₁.wr) (stackArgAddr s 0) 8 := by rw [k₁.2.1, k₁.2.2]; exact ha0
  have hw₁ : InRegions t₁.wr (VG.Proof.Bignum.X86_64.off B (8 * sIn)) 8 := by rw [k₁.2.2]; exact hw sIn (by decide)
  have e0₁ : t₁.gpr .rsp + BitVec.ofInt 64 8 = stackArgAddr s 0 := by rw [k₁.gpr (by decide)]; exact e0
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun t => t.gpr .rdi = B ∧
      t.mem = t₁.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sIn)) (stackArg s 0)) (by
    xrun [State.ea, hdr11, e0₁, ha0₁, hr₁, h11, hdrOff, hw₁]) rfl) fun t ⟨⟨hdi, hm⟩, k₂⟩ => ?_
  refine ⟨hdi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try rw [hm]
  · exact word_skip h0 (by decide) (by decide) (by decide)
  · exact word_skip h1 (by decide) (by decide) (by decide)
  · exact word_skip h2 (by decide) (by decide) (by decide)
  · exact word_skip h3 (by decide) (by decide) (by decide)
  · exact word_skip h4 (by decide) (by decide) (by decide)
  · exact word_skip h5 (by decide) (by decide) (by decide)
  · exact word_skip hO (by decide) (by decide) (by decide)
  · exact word_skip hN (by decide) (by decide) (by decide)
  · exact word_skip hK (by decide) (by decide) (by decide)
  · exact word_skip hE (by decide) (by decide) (by decide)
  · exact word_skip hL (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  · exact Outside.store_hdr ho₁ (by decide) (by decide) _
  · exact (k₁.trans k₂).mono (by decide)

/-! ## The values in `pre` -/

/-- A number from its words. -/
theorem wv_of_words {m : Mem} {p : Addr} {d x : Nat} : ∀ {n : Nat},
    (∀ i < n, (VG.Proof.Bignum.X86_64.word m p (d + 8 * i)).toNat = x / 2 ^ (64 * i) % 2 ^ 64) → wv m p d n = x % 2 ^ (64 * n)
  | 0, _ => by simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | n + 1, h => by
    rw [wv, VG.Proof.Bignum.X86_64.wv_of_words fun i hi => h i (by omega), h n (by omega), pow64_succ, Nat.mod_mul]

/-- The `2 w` words at `pp`, as two numbers of `w` words. -/
theorem pre_words {m : Mem} {pp : Addr} {w N R : Nat}
    (h : Spec.Rsa.wordsAt m pp (2 * w) = Spec.Rsa.toWords N w ++ Spec.Rsa.toWords R w)
    (hN : N < 2 ^ (64 * w)) (hR : R < 2 ^ (64 * w)) :
    wv m pp 0 w = N ∧ wv m pp (8 * w) w = R := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords, Spec.Rsa.toWords, show 2 * w = w + w by omega, List.range_add,
    List.map_append, List.map_map] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  rw [List.map_inj_left] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [← Nat.mod_eq_of_lt hN]
    refine VG.Proof.Bignum.X86_64.wv_of_words fun i hi => ?_
    show (m.readW (pp + BitVec.ofNat 64 (0 + 8 * i)) 64).toNat = _
    rw [Nat.zero_add, h1 i (List.mem_range.mpr hi), BitVec.toNat_ofNat]
  · rw [← Nat.mod_eq_of_lt hR]
    refine VG.Proof.Bignum.X86_64.wv_of_words fun i hi => ?_
    have := h2 i (List.mem_range.mpr hi)
    simp only [Function.comp_apply] at this
    show (m.readW (pp + BitVec.ofNat 64 (8 * w + 8 * i)) 64).toNat = _
    rw [show 8 * w + 8 * i = 8 * (w + i) by omega, this, BitVec.toNat_ofNat]

/-- `pre` holds the values of the valid modulus `nB`. -/
theorem pre_of_some {m : Mem} {pp : Addr} {k : Nat} {nB : List Byte} (hl : nB.length = k) (hk : 64 ≤ k)
    (hpp : Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt m pp (2 * ((k + 7) / 8)))) :
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k = true ∧ wv m pp 0 ((k + 7) / 8) = Spec.Rsa.os2ip nB ∧
      wv m pp (8 * ((k + 7) / 8)) ((k + 7) / 8) = 2 ^ (128 * ((k + 7) / 8)) % Spec.Rsa.os2ip nB := by
  have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k = true := by
    cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k
    · simp [Spec.Rsa.publicPrecompute, hl, hv] at hpp
    · rfl
  rw [publicPrecompute_some hl hv] at hpp
  have hlt : Spec.Rsa.os2ip nB < 2 ^ (64 * ((k + 7) / 8)) := by
    have := os2ip_lt nB
    rw [hl, pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have hpos : 0 < Spec.Rsa.os2ip nB := by
    have := (valid_facts hv hk).2.1; omega
  obtain ⟨h1, h2⟩ := VG.Proof.Bignum.X86_64.pre_words (Option.some.inj hpp).symm hlt (Nat.lt_trans (Nat.mod_lt _ hpos) hlt)
  exact ⟨hv, h1, h2⟩

/-- The checks pass for the values of a valid modulus. -/
theorem checks_true {m : Mem} {B : Addr} {w N : Nat} (hw : 1 ≤ w) (hN : wv m B (VG.Proof.Bignum.X86_64.slot w aN) w = N)
    (hodd : N % 2 = 1) (hlo : 2 ^ (64 * (w - 1)) ≤ N) (hRN : wv m B (VG.Proof.Bignum.X86_64.slot w aR2) w < N) :
    (decide ((VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w aN)).toNat % 2 = 1) &&
      decide (wv m B (VG.Proof.Bignum.X86_64.slot w aR2) w < wv m B (VG.Proof.Bignum.X86_64.slot w aN) w) &&
      decide (VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w aN + 8 * (w - 1)) ≠ 0)) = true := by
  have h1 : (VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ hw, Nat.mod_mod_of_dvd _ (by decide), hN, hodd]
  have h3 : VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w aN + 8 * (w - 1)) ≠ 0 := by
    intro h0
    have h := word_of_wv m B (VG.Proof.Bignum.X86_64.slot w aN) w (q := w - 1) (by omega)
    rw [h0, hN, show (0 : BitVec 64).toNat = 0 from rfl] at h
    have hlt := wv_lt m B (VG.Proof.Bignum.X86_64.slot w aN) w
    rw [hN] at hlt
    have hp : 0 < 2 ^ (64 * (w - 1)) := Nat.two_pow_pos _
    have hq : N / 2 ^ (64 * (w - 1)) < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul hp, ← Nat.pow_add, show 64 + 64 * (w - 1) = 64 * w by omega]; exact hlt
    have hq1 : 1 ≤ N / 2 ^ (64 * (w - 1)) := (Nat.le_div_iff_mul_le hp).mpr (by omega)
    rw [Nat.mod_eq_of_lt hq] at h
    omega
  rw [hN]
  simp only [h1, hRN, decide_true, Bool.and_true, Bool.true_and, decide_eq_true_eq]
  exact h3

/-- What values that pass the checks give: an odd `N > 1`, and `R < N`. -/
theorem checks_facts {m : Mem} {B : Addr} {w : Nat} (hw : 2 ≤ w)
    (h : (decide ((VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w aN)).toNat % 2 = 1) &&
      decide (wv m B (VG.Proof.Bignum.X86_64.slot w aR2) w < wv m B (VG.Proof.Bignum.X86_64.slot w aN) w) &&
      decide (VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w aN + 8 * (w - 1)) ≠ 0)) = true) :
    wv m B (VG.Proof.Bignum.X86_64.slot w aN) w % 2 = 1 ∧ 1 < wv m B (VG.Proof.Bignum.X86_64.slot w aN) w ∧ wv m B (VG.Proof.Bignum.X86_64.slot w aR2) w < wv m B (VG.Proof.Bignum.X86_64.slot w aN) w := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide), wv_mod64 _ _ _ (by omega)]; exact h1, ?_, h2⟩
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h3
  have ht : (VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot (v + 1) aN + 8 * v)).toNat ≠ 0 := fun h0 => h3 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  have hp : 1 < 2 ^ (64 * v) := Nat.one_lt_two_pow (by omega)
  rw [wv]
  have : 2 ^ (64 * v) ≤ 2 ^ (64 * v) * (VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot (v + 1) aN + 8 * v)).toNat :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

/-! ## The whole function -/

/-- What `code` uses of its contract's precondition, for the working space
`B` (the third stack argument) of `Z` bytes, the modulus' length `k` and
`pre`'s `2 w` words. -/
structure PdCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .rsi).toNat
  hk2 : (s.gpr .rsi).toNat ≤ 1024
  hL1 : 1 ≤ (s.gpr .r9).toNat
  hL2 : (s.gpr .r9).toNat ≤ (s.gpr .rsi).toNat
  hpl : (s.gpr .rcx).toNat = 2 * (((s.gpr .rsi).toNat + 7) / 8)
  hZ : 128 * (s.gpr .rsi).toNat ≤ (stackArg s 3).toNat * 8
  hs : VG.Proof.Bignum.X86_64.Scr s (stackArg s 2) ((stackArg s 3).toNat * 8)
  ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8
  ha2 : InRegions (s.rd ++ s.wr) (stackArgAddr s 2) 8
  hsep : ∀ m', VG.Proof.Bignum.X86_64.Outside (stackArg s 2) 0 (8 * 22) s.mem m' → m'.readW (stackArgAddr s 0) 64 = stackArg s 0
  hpr : ∀ i < 2 * (((s.gpr .rsi).toNat + 7) / 8), InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (s.gpr .rdx) (8 * i)) 8
  hps : ∀ j < 16 * (((s.gpr .rsi).toNat + 7) / 8),
    (stackArg s 3).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (stackArg s 2) (s.gpr .rdx + BitVec.ofNat 64 j)
  heb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .r8)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  hxb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
  hout : ∀ j < (s.gpr .rsi).toNat, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .rsi).toNat, (stackArg s 3).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (stackArg s 2) (s.gpr .rdi + BitVec.ofNat 64 j)
  hret : ∀ b < 8, (stackArg s 3).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (stackArg s 2) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    ∀ j < (s.gpr .rsi).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j

theorem pdCtx_of {s : State} (h : pdContract.pre s) : VG.Proof.Bignum.X86_64.PdCtx s := by
  simp only [VG.Proof.Bignum.X86_64.pdContract] at h
  obtain ⟨hsp, hrd, hwr, dOp, dOe, dOi, dOs, dOa, dps, des, dis, dsa, dRo, dRp, dRe, dRi, dRs, dRa,
    wO, wP, wE, wI, wS, hk, hpl, hil, hL1, hL2, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords at hpl
  have hs : VG.Proof.Bignum.X86_64.Scr s (stackArg s 2) ((stackArg s 3).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hpre : (⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hL1, hL2, hpl, by omega, hs,
    ⟨⟨stackArgAddr s 0, 32⟩, by rw [hrd]; simp, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩,
    ⟨⟨stackArgAddr s 0, 32⟩, by rw [hrd]; simp,
      by rw [stackArgAddr_two]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := b) (by omega) (by omega)); omega)),
    fun i hi => ⟨_, hpre, Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj => out_scr dps (contains_byte _ (by omega) (by omega)),
    src_of_region (by rw [hrd]; simp) (by omega) des,
    src_of_region (by rw [hrd, ← hil]; simp) (by omega) (by rw [← hil]; exact dis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega) (by omega)), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, fun j hj he => dRo _ hc (by rw [he]; exact contains_byte _ (by omega) (by omega))⟩

/-- The checks' result, from the numbers in the arrays. -/
def chkv (w N R : Nat) : Bool :=
  decide (N % 2 = 1) && decide (R < N) && decide (N / 2 ^ (64 * (w - 1)) % 2 ^ 64 ≠ 0)

theorem chk_eq {m : Mem} {B : Addr} {w : Nat} (hw : 1 ≤ w) :
    (decide ((VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w aN)).toNat % 2 = 1) &&
      decide (wv m B (VG.Proof.Bignum.X86_64.slot w aR2) w < wv m B (VG.Proof.Bignum.X86_64.slot w aN) w) &&
      decide (VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w aN + 8 * (w - 1)) ≠ 0)) =
      VG.Proof.Bignum.X86_64.chkv w (wv m B (VG.Proof.Bignum.X86_64.slot w aN) w) (wv m B (VG.Proof.Bignum.X86_64.slot w aR2) w) := by
  have h1 : (VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w aN)).toNat % 2 = wv m B (VG.Proof.Bignum.X86_64.slot w aN) w % 2 := by
    rw [← wv_mod64 _ _ _ hw, Nat.mod_mod_of_dvd _ (by decide)]
  have h3 : VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w aN + 8 * (w - 1)) ≠ 0 ↔ wv m B (VG.Proof.Bignum.X86_64.slot w aN) w / 2 ^ (64 * (w - 1)) % 2 ^ 64 ≠ 0 := by
    rw [← word_of_wv m B _ w (q := w - 1) (by omega)]
    exact ⟨fun h h0 => h (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)), fun h h0 => h (by rw [h0]; rfl)⟩
  unfold VG.Proof.Bignum.X86_64.chkv
  rw [h1, decide_eq_decide.mpr h3]

/-- `pre`'s words after the entry, as before it. -/
theorem pre_wv_entry {s t₁ : State} (c : VG.Proof.Bignum.X86_64.PdCtx s)
    (i₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₁.mem) {e : Nat}
    (he : e + 8 * (((s.gpr .rsi).toNat + 7) / 8) ≤ 16 * (((s.gpr .rsi).toNat + 7) / 8)) :
    wv t₁.mem (s.gpr .rdx) e (((s.gpr .rsi).toNat + 7) / 8) = wv s.mem (s.gpr .rdx) e (((s.gpr .rsi).toNat + 7) / 8) :=
  wv_congr fun i hi => Mem.readW_congr fun b hb => i₁ _ (by
    have := c.hps (e + 8 * i + b) (by omega); rwa [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add_ofNat])

/-- `rest`'s hypotheses, after the entry and the load, for values that pass
the checks. -/
theorem pdPre_of {s t₁ t₂ : State} (c : VG.Proof.Bignum.X86_64.PdCtx s) (hdi : t₁.gpr .rdi = stackArg s 2)
    (hO : VG.Proof.Bignum.X86_64.word t₁.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi) (hK : VG.Proof.Bignum.X86_64.word t₁.mem (stackArg s 2) (8 * sK) = s.gpr .rsi)
    (hE : VG.Proof.Bignum.X86_64.word t₁.mem (stackArg s 2) (8 * sE) = s.gpr .r8) (hL : VG.Proof.Bignum.X86_64.word t₁.mem (stackArg s 2) (8 * sElen) = s.gpr .r9)
    (hIn : VG.Proof.Bignum.X86_64.word t₁.mem (stackArg s 2) (8 * sIn) = stackArg s 0)
    (ho₁ : VG.Proof.Bignum.X86_64.Outside (stackArg s 2) 0 (8 * 22) s.mem t₁.mem) (k₁ : VG.Proof.MlKem.X86_64.Keep [.r11, .rax, .rdi] s t₁)
    (hW₂ : VG.Proof.Bignum.X86_64.word t₂.mem (stackArg s 2) (8 * sW) = BitVec.ofNat 64 (((s.gpr .rsi).toNat + 7) / 8))
    (hb₂ : ∀ j < 8, VG.Proof.Bignum.X86_64.word t₂.mem (stackArg s 2) (8 * sArr j) = VG.Proof.Bignum.X86_64.off (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) j))
    (f₂ : Frm (stackArg s 2) (pdLoadRanges (((s.gpr .rsi).toNat + 7) / 8)) t₁.mem t₂.mem) (k₂ : VG.Proof.MlKem.X86_64.Keep mmRegs t₁ t₂)
    (hodd : wv t₂.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8) % 2 = 1)
    (hN1 : 1 < wv t₂.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8))
    (hRN : wv t₂.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aR2) (((s.gpr .rsi).toNat + 7) / 8) <
      wv t₂.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8)) :
    PdPre t₂ (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rsi).toNat (s.gpr .rdi) (s.gpr .r8)
      (stackArg s 0) (s.gpr .r9).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
      (wv t₂.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8))
      (wv t₂.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aR2) (((s.gpr .rsi).toNat + 7) / 8)) := by
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  have hz : VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have x₂ := Fixed.of_frm f₂ (pdLoadRanges_fixed _)
  have i₂ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₂.mem :=
    (InScr.of_outside ho₁ (by omega)).trans (InScr.of_frm f₂ fun r hr => (pdLoadRanges_le _ r hr).trans hz)
  have kk := k₁.trans k₂
  exact
    { scr := c.hs.congr kk.2.2, rdi := (k₂.gpr (by decide)).trans hdi, z := hz, k1 := hk1, k2 := hk2,
      hO := by rw [x₂ sOut (by decide)]; exact hO, hK := by rw [x₂ sK (by decide), hK, VG.Proof.Bignum.X86_64.ofNat_toNat64],
      hE := by rw [x₂ sE (by decide)]; exact hE, hL := by rw [x₂ sElen (by decide), hL, VG.Proof.Bignum.X86_64.ofNat_toNat64],
      hIn := by rw [x₂ sIn (by decide)]; exact hIn, hW := hW₂, hb := hb₂, n := rfl, r := rfl, odd := hodd,
      n1 := hN1, rlt := hRN, x := c.hxb.congrK i₂ kk, e := c.heb.congrK i₂ kk, xl := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _,
      el := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, L1 := c.hL1, L2 := c.hL2, out := fun j hj => by rw [kk.2.2]; exact c.hout j hj,
      outSep := c.houts }

theorem pdCode_correct (M : Mont)
    (hmx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (h : pdContract.pre s) :
    ∃ t s', Exec isa (Precomputed.code M.mm) s t s' ∧ abiPreserved s s' ∧ pdContract.post s s' := by
  have c := VG.Proof.Bignum.X86_64.pdCtx_of h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  suffices hwp : WP isa (Precomputed.code M.mm) s fun s' => gprPreserved s s' ∧ pdContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold Precomputed.code
  have hw : ∀ i < 22, InRegions s.wr (VG.Proof.Bignum.X86_64.off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.pdEntry_ok rfl hw c.ha0 c.ha2 c.hsep) fun t₁ ⟨hdi, h0, h1, h2, h3, h4, h5, hO, hN, hK,
    hE, hL, hIn, ho₁, k₁⟩ => ?_)
  have i₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
  have hz : VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  refine WP.seq (WP.mono (pdLoad_ok (c.hs.congr k₁.2.2) hdi hz (by omega) (by omega) (by rw [hK, VG.Proof.Bignum.X86_64.ofNat_toNat64])
    hN (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact c.hpr i hi) c.hps)
    fun t₂ ⟨hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩ => ?_)
  rw [VG.Proof.Bignum.X86_64.pre_wv_entry c i₁ (by omega)] at hN₂
  rw [VG.Proof.Bignum.X86_64.pre_wv_entry c i₁ (by omega)] at hR₂
  have x₂ := Fixed.of_frm f₂ (pdLoadRanges_fixed _)
  have i₂ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₂.mem :=
    i₁.trans (InScr.of_frm f₂ fun r hr => (pdLoadRanges_le _ r hr).trans hz)
  have kk := k₁.trans k₂
  have hs₂ := c.hs.congr kk.2.2
  have hdi₂ : t₂.gpr .rdi = stackArg s 2 := (k₂.gpr (by decide)).trans hdi
  have hO₂ : VG.Proof.Bignum.X86_64.word t₂.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi := by rw [x₂ sOut (by decide)]; exact hO
  have hK₂ : VG.Proof.Bignum.X86_64.word t₂.mem (stackArg s 2) (8 * sK) = BitVec.ofNat 64 (s.gpr .rsi).toNat := by
    rw [x₂ sK (by decide), hK, VG.Proof.Bignum.X86_64.ofNat_toNat64]
  have hout₂ : ∀ j < (s.gpr .rsi).toNat, InRegions t₂.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [kk.2.2]; exact c.hout j hj
  -- What either branch leaves.
  have fin : ∀ t r (cb : Bool),
      MainPost t₂ t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rsi).toNat (s.gpr .rdi) r cb →
      (∀ nB : List Byte, nB.length = (s.gpr .rsi).toNat →
        Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) (s.gpr .rsi).toNat = true →
        wv s.mem (s.gpr .rdx) 0 (((s.gpr .rsi).toNat + 7) / 8) = Spec.Rsa.os2ip nB →
        wv s.mem (s.gpr .rdx) (8 * (((s.gpr .rsi).toNat + 7) / 8)) (((s.gpr .rsi).toNat + 7) / 8) =
          2 ^ (128 * (((s.gpr .rsi).toNat + 7) / 8)) % Spec.Rsa.os2ip nB →
        cb = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) < Spec.Rsa.os2ip nB) ∧
        r = if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) < Spec.Rsa.os2ip nB then
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) ^
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) % Spec.Rsa.os2ip nB else 0) →
      gprPreserved s t ∧ pdContract.post s t := by
    intro t r cb hp H
    refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, fun nB hl hpp => ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hp.saved 0 (by decide)).trans ((x₂ 0 (by decide)).trans h0)
      · exact (hp.saved 1 (by decide)).trans ((x₂ 1 (by decide)).trans h1)
      · exact (hp.keep.gpr (by decide)).trans (kk.gpr (by decide))
      · exact (hp.saved 2 (by decide)).trans ((x₂ 2 (by decide)).trans h2)
      · exact (hp.saved 3 (by decide)).trans ((x₂ 3 (by decide)).trans h3)
      · exact (hp.saved 4 (by decide)).trans ((x₂ 4 (by decide)).trans h4)
      · exact (hp.saved 5 (by decide)).trans ((x₂ 5 (by decide)).trans h5)
    · obtain ⟨hZx, hne⟩ := c.hret b hb
      rw [hp.frame _ hZx hne, i₂ _ hZx]
    · rw [c.hpl] at hpp
      obtain ⟨hv, hNv, hRv⟩ := VG.Proof.Bignum.X86_64.pre_of_some hl hk1 hpp
      exact written_of hl hp.bytes hp.rax (fun _ => H nB hl hv hNv hRv) fun h => absurd h (by rw [hv]; decide)
  generalize hcb : (decide ((VG.Proof.Bignum.X86_64.word t₂.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aN)).toNat % 2 = 1) &&
      decide (wv t₂.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aR2) (((s.gpr .rsi).toNat + 7) / 8) <
        wv t₂.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8)) &&
      decide (VG.Proof.Bignum.X86_64.word t₂.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aN + 8 * ((((s.gpr .rsi).toNat + 7) / 8) - 1)) ≠ 0))
    = cb at hz₂
  refine WP.ite (!cb) (by simp [VG.X86_64.eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · -- Values of no modulus.
    have hcf : cb = false := by simpa using hb
    refine WP.mono (fail_ok hs₂ hdi₂ (by omega) (by omega) (by omega) hO₂ hK₂ hout₂ c.houts)
      fun t hp => fin t 0 false hp fun nB hl hv hNv hRv => ?_
    obtain ⟨hodd, -, hlo⟩ := valid_facts hv hk1
    have := VG.Proof.Bignum.X86_64.checks_true (by omega) (hN₂.trans hNv) hodd hlo
      (by rw [hR₂, hRv]; exact Nat.mod_lt _ (by omega))
    rw [hcb, hcf] at this
    exact absurd this (by decide)
  · have hct : cb = true := by simpa using hb
    rw [hct] at hcb
    obtain ⟨hodd, hN1, hRN⟩ := VG.Proof.Bignum.X86_64.checks_facts (by omega) hcb
    have hpre := VG.Proof.Bignum.X86_64.pdPre_of c hdi hO hK hE hL hIn ho₁ k₁ hW₂ hb₂ f₂ k₂ hodd hN1 hRN
    refine WP.mono (pdRest_ok hpre) fun t ⟨x, hx, hp⟩ => fin t _ _ hp fun nB hl hv hNv hRv => ?_
    rw [hN₂.trans hNv] at hx hp ⊢
    have hxX := hx (by
      rw [hR₂, hRv, Nat.mod_mod, ← Nat.pow_add, show 128 * (((s.gpr .rsi).toNat + 7) / 8) =
        64 * (((s.gpr .rsi).toNat + 7) / 8) + 64 * (((s.gpr .rsi).toNat + 7) / 8) by omega])
    refine ⟨rfl, ?_⟩
    rw [Nat.pow_mod, hxX, ← Nat.pow_mod]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PdCTExp`. -/
section

/-!
# `vg_rsa_public_precomputed` on x86-64: the exponentiation is constant time but for `e`

Besides the bits of `e` (as in `CTExp.lean`), the exponentiation branches on
whether it has started, which is whether the prefix of `e` so far is
nonzero: the runs agree on it because they agree on `e` (`pExpBit_ct`,
`pExpLoop_ct`, `finish_ct`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Precomputed
open VG.Proof.MlKem.X86_64

variable {M : Mont}

/-! ## A bit -/

/-- The public data of a bit: the working space, `m`, the prefix `E` of `e`
so far and the bit's byte (shifted) `V`. -/
structure PBitPub where
  L : Lay
  N : Nat
  E : Nat
  V : Nat

/-- What every step needs of the working space and `X ≡ x R`. -/
def PFacts (L : Lay) (N X x : Nat) : Prop :=
  VG.Proof.Bignum.X86_64.slot L.w 8 ≤ L.Z ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31 ∧ Nat.Coprime (2 ^ (64 * L.w)) N ∧ X < N ∧
    X % N = x * 2 ^ (64 * L.w) % N

/-- Before a step of a bit, after the prefix `E`. -/
def PQ (p : VG.Proof.Bignum.X86_64.PBitPub) (t : State) : Prop :=
  ∃ X x, ExpCtx t p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ YSt t.mem p.L.B p.L.w p.N x p.E ∧ VG.Proof.Bignum.X86_64.PFacts p.L p.N X x ∧
    VG.Proof.Bignum.X86_64.word t.mem p.L.B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 p.V ∧ p.V < 2 ^ 62

theorem pins_PQ : Pins VG.Proof.Bignum.X86_64.PQ [.rdi] := fun _ _ _ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.rdi, h₂.good.rdi]

theorem PQ.goodL {p : VG.Proof.Bignum.X86_64.PBitPub} {t : State} (h : VG.Proof.Bignum.X86_64.PQ p t) : GoodL p.L t :=
  let ⟨_, _, hc, _, hf, _⟩ := h; ⟨hc.good, hf.1⟩

/-- The started test keeps `PQ`. -/
theorem startedTest_pq {p : VG.Proof.Bignum.X86_64.PBitPub} {t : State} (h : VG.Proof.Bignum.X86_64.PQ p t) :
    WP isa (.block startedTest) t fun t' => VG.Proof.Bignum.X86_64.PQ p t' ∧ t'.zf = some (decide (p.E = 0)) := by
  obtain ⟨X, x, hc, hy, hf, hV, hV'⟩ := h
  exact WP.mono (startedTest_ok hc.good hf.1 hy) fun t' ⟨hz, hm, k⟩ =>
    ⟨⟨X, x, hc.mem hm k (by decide), by rw [hm]; exact hy, hf, by rw [hm]; exact hV, hV'⟩, hz⟩

/-- `start` leaks the same in runs with the same working space. -/
theorem start_ct : RelCT isa (Two GoodL) start fun _ _ => True := by
  unfold start
  refine RelCT.seq (two_piece (Ψ := fun (L : Lay) t => t.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aXm) ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aY) ∧ t.gpr .rdi = L.B) [.rdi]
    pins_good (by taint_decide) ?_)
    (two_taint [.rsi, .rbx, .r12, .rdi] (fun L s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide))
  rintro L t ⟨hg, hZ⟩
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off L.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  refine WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t₁ => t₁.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t₁.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aXm) ∧ t₁.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aY)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aXm) (by decide),
      hl (sArr aY) (by decide), hg.hdr.hw, hg.hdr.harr aXm (by decide), hg.hdr.harr aY (by decide)]) rfl)
    fun t₁ ⟨⟨h12, hsi, hbx⟩, k⟩ => ⟨h12, hsi, hbx, (k.gpr (by decide)).trans hg.rdi⟩

/-- A bit leaks the same in runs that agree on `e`. -/
theorem pExpBit_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.PQ) (Precomputed.expBit M.mm) fun _ _ => True := by
  unfold Precomputed.expBit
  -- Whether started.
  refine RelCT.seq (two_piece (Ψ := fun p t => VG.Proof.Bignum.X86_64.PQ p t ∧ t.zf = some (decide (p.E = 0))) _ VG.Proof.Bignum.X86_64.pins_PQ
    (by taint_decide) fun p t h => VG.Proof.Bignum.X86_64.startedTest_pq h) ?_
  -- `Y := Y²` if started.
  refine RelCT.seq (R := Two fun (p : VG.Proof.Bignum.X86_64.PBitPub) t => VG.Proof.Bignum.X86_64.PQ ⟨p.L, p.N, 2 * p.E, p.V⟩ t)
    (two_post (two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [VG.X86_64.eval, h₁.2, h₂.2])
      (two_map (·.L) (fun _ _ h => h.1.1.goodL) (M.ctL (by unfold MmUse; decide)))
      (RelCT.block_nil fun _ _ _ => trivial)) ?_) ?_
  · rintro p t ⟨⟨X, x, hc, hy, hf, hV, hV'⟩, hz⟩
    exact WP.mono (pSq_ok hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hy hz) fun t' ⟨hc', hy', ha, _⟩ =>
      ⟨X, x, hc', hy', hf, by rw [ha.hslot (by decide)]; exact hV, hV'⟩
  -- The bit.
  refine RelCT.seq (two_piece (Ψ := fun (p : VG.Proof.Bignum.X86_64.PBitPub) t => VG.Proof.Bignum.X86_64.PQ ⟨p.L, p.N, 2 * p.E, p.V⟩ t ∧
      t.zf = some (decide (p.V / 128 % 2 = 0))) [.rdi] (fun p s₁ s₂ h₁ h₂ => VG.Proof.Bignum.X86_64.pins_PQ _ s₁ s₂ h₁ h₂)
    (by taint_decide) ?_) ?_
  · rintro p t ⟨X, x, hc, hy, hf, hV, hV'⟩
    exact WP.mono (bitTest_ok hc.good hf.1 hV (by omega)) fun t' ⟨hz, hm, k⟩ =>
      ⟨⟨X, x, hc.mem hm k (by decide), by rw [hm]; exact hy, hf, by rw [hm]; exact hV, hV'⟩, hz⟩
  -- If the bit is set: `Y := Y X` once started, `Y := X` and started if not; then the next bit.
  refine RelCT.seq (R := Two fun (p : VG.Proof.Bignum.X86_64.PBitPub) t => t.gpr .rdi = p.L.B)
    (two_post (two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [VG.X86_64.eval, h₁.2, h₂.2]) ?_
      (RelCT.block_nil fun _ _ _ => trivial)) ?_)
    (two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))
  · refine RelCT.seq (two_piece (Ψ := fun (p : VG.Proof.Bignum.X86_64.PBitPub) t => VG.Proof.Bignum.X86_64.PQ ⟨p.L, p.N, 2 * p.E, p.V⟩ t ∧
        t.zf = some (decide (2 * p.E = 0))) [.rdi] (fun p s₁ s₂ h₁ h₂ => VG.Proof.Bignum.X86_64.pins_PQ _ s₁ s₂ h₁.1.1 h₂.1.1)
      (by taint_decide) fun p t h => VG.Proof.Bignum.X86_64.startedTest_pq h.1.1) ?_
    refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [VG.X86_64.eval, h₁.2, h₂.2]) ?_ ?_
    · exact two_map (fun (p : VG.Proof.Bignum.X86_64.PBitPub) => p.L) (fun _ _ h => h.1.1.goodL)
        (M.ctL (by unfold MmUse; decide))
    · exact two_map (fun (p : VG.Proof.Bignum.X86_64.PBitPub) => p.L) (fun _ _ h => h.1.1.goodL) VG.Proof.Bignum.X86_64.start_ct
  · rintro p t ⟨⟨X, x, hc, hy, hf, -, -⟩, hz⟩
    exact WP.mono (pMul_ok hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 hy hz)
      fun t' ⟨hc', _⟩ => hc'.good.rdi

/-! ## The bits of a byte -/

/-- After `j` bits of a byte. -/
def PBitsInv (p : BitsPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (X x : Nat), PBitInv t₀ p.L.B p.L.Z p.L.w p.L.minv p.N X x p.E p.v j s ∧
    VG.Proof.Bignum.X86_64.PFacts p.L p.N X x ∧ p.v < 256

theorem pBitsInv_pq {p : BitsPub} {j : Nat} {s : State} (hj : j < 8) (h : VG.Proof.Bignum.X86_64.PBitsInv p j s) :
    VG.Proof.Bignum.X86_64.PQ ⟨p.L, p.N, p.E * 2 ^ j + p.v / 2 ^ (8 - j), p.v * 2 ^ j⟩ s := by
  obtain ⟨t₀, X, x, hI, hf, hv⟩ := h
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨X, x, hI.ctx, hI.y, hf, hI.v, by have := Nat.mul_le_mul_left p.v hp; dsimp only; omega⟩

/-- The eight bits of a byte leak the same in runs that agree on `e`. -/
theorem pBits_ct : RelCT isa (Two fun p s => 0 < 8 ∧ VG.Proof.Bignum.X86_64.PBitsInv p 0 s) (.loop (Precomputed.expBit M.mm) .ne)
    (Two fun p s => VG.Proof.Bignum.X86_64.PBitsInv p 8 s) :=
  two_loop (Φ := VG.Proof.Bignum.X86_64.PBitsInv) (fun _ => 8)
    (two_map (fun q : BitsPub × Nat =>
      (⟨q.1.L, q.1.N, q.1.E * 2 ^ q.2 + q.1.v / 2 ^ (8 - q.2), q.1.v * 2 ^ q.2⟩ : VG.Proof.Bignum.X86_64.PBitPub))
      (fun _ _ h => VG.Proof.Bignum.X86_64.pBitsInv_pq h.1 h.2) VG.Proof.Bignum.X86_64.pExpBit_ct)
    fun _ _ _ hj ⟨t₀, X, x, hI, hf, hv⟩ =>
      WP.mono (pBitStep_ok hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 hv hj hI) fun _ ⟨hz, hI'⟩ =>
        ⟨eval_ne_count hj hz, fun _ => ⟨t₀, X, x, hI', hf, hv⟩, fun h => h ▸ ⟨t₀, X, x, hI', hf, hv⟩⟩

/-! ## The bytes of `e` -/

/-- After `i` bytes of `e`. -/
def PBytesInv (a : EPub) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (X x : Nat), PByteInv t₀ a.L.B a.L.Z a.L.w a.L.minv a.N X x a.ep a.len a.eb i s ∧
    EFacts a X x ∧ ESrc a t₀

/-- After `byteHead`'s loads. -/
def PHeadMid (q : EPub × Nat) (s : State) : Prop :=
  q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.PBytesInv q.1 q.2 s ∧ s.gpr .rax = q.1.ep ∧ s.gpr .rcx = BitVec.ofNat 64 q.2

theorem pins_pBytes : Pins (fun (q : EPub × Nat) s => q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.PBytesInv q.1 q.2 s) [.rdi] :=
  fun _ _ _ ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.rdi, h₂.ctx.good.rdi]

theorem pins_pHeadMid : Pins VG.Proof.Bignum.X86_64.PHeadMid [.rdi, .rax, .rcx] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨-, ⟨_, _, _, i₁, _⟩, a₁, c₁⟩ := h₁
  obtain ⟨-, ⟨_, _, _, i₂, _⟩, a₂, c₂⟩ := h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [i₁.ctx.good.rdi, i₂.ctx.good.rdi]
  · rw [a₁, a₂]
  · rw [c₁, c₂]

/-- One byte of `e` leaks the same in runs that agree on `e`. -/
theorem pByteBody_ct : RelCT isa (Two fun (q : EPub × Nat) s => q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.PBytesInv q.1 q.2 s)
    (.seq (.block byteHead) (.seq (.loop (Precomputed.expBit M.mm) .ne) (.block byteNext))) fun _ _ => True := by
  rw [byteHead_eq]
  have w₁ : ∀ (q : EPub × Nat) s, q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.PBytesInv q.1 q.2 s →
      WP isa (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr VG.Impl.Bignum.X86_64.Public.sI))]) s (VG.Proof.Bignum.X86_64.PHeadMid q) := by
    rintro q s ⟨hi, t₀, X, x, hI, hf, hsrc⟩
    exact WP.mono (pByteHead1_ok hf.1 hI) fun t ⟨h1, h2, h3⟩ => ⟨hi, ⟨t₀, X, x, h3, hf, hsrc⟩, h1, h2⟩
  have w₂ : ∀ (q : EPub × Nat) s, VG.Proof.Bignum.X86_64.PHeadMid q s →
      WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr VG.Impl.Bignum.X86_64.Public.sV) .rax,
        .mov32 .rax (.imm 8), .store (hdr VG.Impl.Bignum.X86_64.Public.sBit) .rax]) s fun t => 0 < 8 ∧ VG.Proof.Bignum.X86_64.PBitsInv (bitsPub q) 0 t := by
    rintro q s ⟨hi, ⟨t₀, X, x, hI, hf, hsrc⟩, hax, hcx⟩
    refine WP.mono (pByteHead2_ok hf.1 hsrc.1 hi hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2 hI hax hcx)
      fun t ⟨_, _, hB⟩ => ⟨by decide, t, X, x, ?_, hf, ?_⟩
    · simp only [bitsPub, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show q.2 < q.1.eb.length by have := hsrc.1; omega), Option.getD_some]
      exact hB
    · simp only [bitsPub]; exact (List.getD q.1.eb q.2 0).isLt
  have h₁ : RelCT isa (Two fun (q : EPub × Nat) s => q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.PBytesInv q.1 q.2 s)
      (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr VG.Impl.Bignum.X86_64.Public.sI))]) (Two VG.Proof.Bignum.X86_64.PHeadMid) :=
    two_piece _ VG.Proof.Bignum.X86_64.pins_pBytes (by taint_decide) w₁
  have h₂ : RelCT isa (Two VG.Proof.Bignum.X86_64.PHeadMid) (.block [.movzx8 .rax { base := .rax, index := some .rcx },
      .store (hdr VG.Impl.Bignum.X86_64.Public.sV) .rax, .mov32 .rax (.imm 8), .store (hdr VG.Impl.Bignum.X86_64.Public.sBit) .rax])
      (Two fun q s => 0 < 8 ∧ VG.Proof.Bignum.X86_64.PBitsInv (bitsPub q) 0 s) :=
    two_piece _ VG.Proof.Bignum.X86_64.pins_pHeadMid (by taint_decide) w₂
  have h₃ : RelCT isa (Two fun (p : BitsPub) s => VG.Proof.Bignum.X86_64.PBitsInv p 8 s) (.block byteNext) fun _ _ => True :=
    two_taint [.rdi] (fun (_ : BitsPub) s₁ s₂ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.rdi, h₂.ctx.good.rdi]) (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq h₁ h₂))
    (RelCT.seq (two_map bitsPub (fun _ _ h => h) VG.Proof.Bignum.X86_64.pBits_ct) h₃)

/-- Before `expLoop`. -/
def PExpPre (a : EPub) (s : State) : Prop :=
  ∃ X x : Nat, ExpCtx s a.L.B a.L.Z a.L.w a.L.minv a.N X ∧ EFacts a X x ∧
    VG.Proof.Bignum.X86_64.word s.mem a.L.B (8 * sE) = a.ep ∧ VG.Proof.Bignum.X86_64.word s.mem a.L.B (8 * sElen) = BitVec.ofNat 64 a.len ∧
    1 ≤ a.len ∧ ESrc a s

/-- The exponentiation leaks the same in runs that agree on `e`. -/
theorem pExpLoop_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.PExpPre) (Precomputed.expLoop M.mm) (Two fun a s => VG.Proof.Bignum.X86_64.PBytesInv a a.len s) := by
  unfold Precomputed.expLoop
  refine RelCT.seq (two_piece (Ψ := fun a s => 0 < a.len ∧ VG.Proof.Bignum.X86_64.PBytesInv a 0 s) [.rdi]
    (fun _ _ _ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.rdi, h₂.good.rdi]) (by taint_decide) ?_) ?_
  · rintro a s ⟨X, x, hc, hf, he, hlen, hL1, hsrc⟩
    exact WP.mono (pExpInit_ok (x := x) (eb := a.eb) hc hf.1 he hlen) fun t h => ⟨hL1, s, X, x, h, hf, hsrc⟩
  · refine two_loop (Φ := VG.Proof.Bignum.X86_64.PBytesInv) (fun a => a.len) VG.Proof.Bignum.X86_64.pByteBody_ct ?_
    rintro a i s hi ⟨t₀, X, x, hI, hf, hsrc⟩
    exact WP.mono (pByte_ok hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 hsrc.1 hsrc.2.1 hi
      hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2 hI) fun s' ⟨hz, hI'⟩ =>
        ⟨eval_ne_count hi hz, fun _ => ⟨t₀, X, x, hI', hf, hsrc⟩, fun h => h ▸ ⟨t₀, X, x, hI', hf, hsrc⟩⟩

/-! ## The result -/

/-- The public data of `finish`: the working space, `m` and `e`. -/
structure FPub where
  L : Lay
  N : Nat
  E : Nat

/-- Before `finish`. -/
def FPre (p : VG.Proof.Bignum.X86_64.FPub) (s : State) : Prop :=
  ∃ X x, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ YSt s.mem p.L.B p.L.w p.N x p.E ∧
    VG.Proof.Bignum.X86_64.slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31

theorem pins_FPre : Pins VG.Proof.Bignum.X86_64.FPre [.rdi] := fun _ _ _ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.rdi, h₂.good.rdi]

/-- `finish` leaks the same in runs that agree on `e`. -/
theorem finish_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.FPre) (Precomputed.finish M.mm) fun _ _ => True := by
  unfold Precomputed.finish
  refine RelCT.seq (two_piece (Ψ := fun p t => VG.Proof.Bignum.X86_64.FPre p t ∧ t.zf = some (decide (p.E = 0))) _ VG.Proof.Bignum.X86_64.pins_FPre
    (by taint_decide) ?_) ?_
  · rintro p t ⟨X, x, hc, hy, hZ, hw, hw'⟩
    exact WP.mono (startedTest_ok hc.good hZ hy) fun t' ⟨hz, hm, k⟩ =>
      ⟨⟨X, x, hc.mem hm k (by decide), by rw [hm]; exact hy, hZ, hw, hw'⟩, hz⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [VG.X86_64.eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map (fun (p : VG.Proof.Bignum.X86_64.FPub) => p.L) (fun _ _ ⟨⟨⟨_, _, hc, _, hZ, _⟩, _⟩, _⟩ => ⟨hc.good, hZ⟩)
      (M.ctL (by unfold MmUse; decide))
  -- `Y := 1`.
  unfold setWord
  refine RelCT.seq (two_piece (Ψ := fun (p : VG.Proof.Bignum.X86_64.FPub) t => GoodL p.L t ∧ t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧
      t.gpr .rcx = BitVec.ofNat 64 0) [.rdi] (fun p s₁ s₂ h₁ h₂ => VG.Proof.Bignum.X86_64.pins_FPre p s₁ s₂ h₁.1.1 h₂.1.1)
    (by taint_decide) ?_) ?_
  · rintro p t ⟨⟨⟨X, x, hc, hy, hZ, hw, hw'⟩, _⟩, _⟩
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off p.L.B (8 * i)) 8 := fun i hi =>
      hc.good.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hc.good.scr.nowrap; omega)
    refine WP.mono (WP.keep [.r12, .rdx, .rcx] (Q := fun t₂ => t₂.gpr .r12 = BitVec.ofNat 64 p.L.w ∧
        t₂.gpr .rcx = BitVec.ofNat 64 0 ∧ t₂.mem = t.mem) (by
      xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl sW (by decide), hc.good.hdr.hw]) rfl)
      fun t₂ ⟨⟨h12, hcx, hm⟩, k⟩ => ⟨⟨(hc.mem hm k (by decide)).good, hZ⟩, h12, hcx⟩
  refine RelCT.seq (two_piece (Ψ := fun (p : VG.Proof.Bignum.X86_64.FPub) t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aY) ∧
      t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .rcx = BitVec.ofNat 64 0) [.rdi]
    (fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1) (by taint_decide) ?_)
    (two_taint [.r8, .r12, .rcx] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
  rintro p t ⟨⟨hg, hZ⟩, h12, hcx⟩
  have hl : InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off p.L.B (8 * sArr aY)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot p.L.w 8 (show sArr aY < 32 by decide); have := hg.scr.nowrap; omega)
  refine WP.mono (WP.keep [.r8] (Q := fun t' => t'.gpr .r8 = VG.Proof.Bignum.X86_64.off p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aY)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.harr aY (by decide)]) rfl)
    fun t' ⟨h8, k⟩ => ⟨h8, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PdCT`. -/
section

/-!
# `vg_rsa_public_precomputed` on x86-64: constant time but for `pre` and `e`

Every piece's addresses and branches depend only on the pointers, the
lengths, `pre` and `e`: the load and the checks of `pre` (`pdLoad_ct`),
`rest` (`pdRest_ct`), and the whole function (`pdCode_constantTime`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

variable {M : Mont}

/-! ## `rest` -/

/-- The public data of `rest`: the working space, `k`, the pointers, `e`
and the values `N` and `R` in the arrays. -/
structure DPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  ep : Addr
  ip : Addr
  len : Nat
  eb : List Byte
  N : Nat
  R : Nat

/-- `pdRest_ok`'s hypotheses. -/
def DRel (p : VG.Proof.Bignum.X86_64.DPub) (s : State) : Prop :=
  ∃ xb, PdPre s p.B p.Z p.k p.op p.ep p.ip p.len p.eb xb p.N p.R

/-- From `σ`, at `rest`'s start, to `t`: what changed, and the mask. -/
def DG (p : VG.Proof.Bignum.X86_64.DPub) (xb : List Byte) (σ t : State) : Prop :=
  PdPre σ p.B p.Z p.k p.op p.ep p.ip p.len p.eb xb p.N p.R ∧ Frm p.B (pdAll ((p.k + 7) / 8)) σ.mem t.mem ∧
    VG.Proof.MlKem.X86_64.Keep mmRegs σ t ∧ VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sMask) = VG.Proof.Bignum.X86_64.mask (decide (Spec.Rsa.os2ip xb < p.N))

theorem PdPre.mem {s t : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte}
    {N R : Nat} (h : PdPre s B Z k op ep ip L eb xb N R) (hm : t.mem = s.mem) {regs : List Reg} (kp : VG.Proof.MlKem.X86_64.Keep regs s t)
    (hr : .rdi ∉ regs) : PdPre t B Z k op ep ip L eb xb N R :=
  { scr := h.scr.congr kp.2.2, rdi := (kp.gpr hr).trans h.rdi, z := h.z, k1 := h.k1, k2 := h.k2,
    hO := hm ▸ h.hO, hK := hm ▸ h.hK, hE := hm ▸ h.hE, hL := hm ▸ h.hL, hIn := hm ▸ h.hIn, hW := hm ▸ h.hW,
    hb := hm ▸ h.hb, n := hm ▸ h.n, r := hm ▸ h.r, odd := h.odd, n1 := h.n1, rlt := h.rlt,
    x := h.x.congrK (by rw [hm]; exact InScr.refl _ _ _) kp, e := h.e.congrK (by rw [hm]; exact InScr.refl _ _ _) kp,
    xl := h.xl, el := h.el, L1 := h.L1, L2 := h.L2, out := fun j hj => by rw [kp.2.2]; exact h.out j hj,
    outSep := h.outSep }

theorem DG.step {p : VG.Proof.Bignum.X86_64.DPub} {xb : List Byte} {σ t t' : State} (h : VG.Proof.Bignum.X86_64.DG p xb σ t)
    (hf : Frm p.B (pdAll ((p.k + 7) / 8)) t.mem t'.mem) (k : VG.Proof.MlKem.X86_64.Keep mmRegs t t')
    (hm : VG.Proof.Bignum.X86_64.word t'.mem p.B (8 * sMask) = VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sMask)) : VG.Proof.Bignum.X86_64.DG p xb σ t' :=
  ⟨h.1, h.2.1.trans hf, (h.2.2.1.trans k).mono (by decide), hm.trans h.2.2.2⟩

theorem DG.fixed {p : VG.Proof.Bignum.X86_64.DPub} {xb : List Byte} {σ t : State} (h : VG.Proof.Bignum.X86_64.DG p xb σ t) : Fixed p.B σ.mem t.mem :=
  Fixed.of_frm h.2.1 (pdAll_fixed _)

theorem DG.inScr {p : VG.Proof.Bignum.X86_64.DPub} {xb : List Byte} {σ t : State} (h : VG.Proof.Bignum.X86_64.DG p xb σ t) : InScr p.B p.Z σ.mem t.mem :=
  InScr.of_frm h.2.1 fun r hr => (pdAll_le _ r hr).trans h.1.z

/-- After the input's registers. -/
def DIn (p : VG.Proof.Bignum.X86_64.DPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.DRel p s ∧ s.gpr .rsi = p.ip ∧ s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) aX)

/-- The input leaks the same in runs with the same public data. -/
theorem pdIn_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.DRel) (seqs pdIn) (Two fun (p : VG.Proof.Bignum.X86_64.DPub) s => SR ⟨p.B, p.Z, ((p.k + 7) / 8)⟩ s) := by
  unfold pdIn
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.DIn) [.rdi] (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]) (by taint_decide) ?_) ?_
  · rintro p s ⟨xb, h⟩
    have hn := h.scr.nowrap
    have hZ : VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) 8 ≤ p.Z := h.z
    obtain ⟨g0, g8⟩ := slot0_ge ((p.k + 7) / 8)
    refine WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = p.ip ∧
        t.gpr .rcx = BitVec.ofNat 64 p.k ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) aX) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sIn) (by unfold sIn sFn; omega),
        h.scr.ld (d := 8 * sK) (by unfold sK sFn; omega), h.scr.ld (d := 8 * sArr aX) (by unfold sArr aX; omega),
        h.hIn, h.hK, h.hb aX (by decide)]) rfl)
      fun t ⟨⟨hsi, hcx, hbx, hm⟩, k⟩ => ⟨⟨xb, h.mem hm k (by decide)⟩, hsi, hcx, hbx⟩
  rw [seqs_one]
  refine two_piece [.rsi, .rcx, .rbx] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide) ?_
  rintro p s ⟨⟨xb, h⟩, hsi, hcx, hbx⟩
  have hk1 := h.k1
  have hk2 := h.k2
  have hn := h.scr.nowrap
  have hZ : VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) 8 ≤ p.Z := h.z
  have hn' : p.B.toNat + VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hw : 2 ≤ ((p.k + 7) / 8) := by show 2 ≤ (p.k + 7) / 8; omega
  refine WP.mono (loadArr_ok h.scr (by decide) h.z h.x h.xl (by omega) (by omega) hsi hcx hbx)
    fun t ⟨_, ha, k⟩ => ⟨h.scr.congr k.2.2, (k.gpr (by decide)).trans h.rdi, h.z,
      hw, show ((p.k + 7) / 8) < 2 ^ 31 by show (p.k + 7) / 8 < 2 ^ 31; omega,
      by rw [ha.hslot (by decide)]; exact h.hW, fun j hj => by rw [ha.hslot (by unfold sArr; omega)]; exact h.hb j hj, ?_⟩
  rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega),
    ← wv_mod64 _ _ _ (show 1 ≤ ((p.k + 7) / 8) by omega), Nat.mod_mod_of_dvd _ (by decide), h.n, h.odd]

/-- After the setup, for `-m⁻¹ = q.2`. -/
def DA (q : VG.Proof.Bignum.X86_64.DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, VG.Proof.Bignum.X86_64.DG q.1 xb σ t ∧ SetupOut t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 q.1.N (Spec.Rsa.os2ip xb) ∧
    wv t.mem q.1.B (VG.Proof.Bignum.X86_64.slot ((q.1.k + 7) / 8) aR2) ((q.1.k + 7) / 8) = q.1.R

/-- The setup leaks the same in runs with the same public data. -/
theorem pdSetup_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.DRel) (seqs (pdIn ++ restSteps)) (Two VG.Proof.Bignum.X86_64.DA) := by
  refine two_post (Ψ := fun p t => ∃ mi, VG.Proof.Bignum.X86_64.DA (p, mi) t)
    (RelCT.seqs_append (by simp [pdIn]) (by simp [restSteps]) (RelCT.seq VG.Proof.Bignum.X86_64.pdIn_ct (two_map (fun p : VG.Proof.Bignum.X86_64.DPub => (⟨p.B, p.Z, ((p.k + 7) / 8)⟩ : RPub)) (fun _ _ h => h) setupRest_ct))) ?_ |>.mono
      (fun _ _ h => h) fun _ _ h => two_bind (fun p t₁ t₂ H₁ H₂ => ?_) h
  · rintro p s ⟨xb, h⟩
    exact WP.mono (pdSetup_ok h) fun t ⟨mi, so, f, k, hR⟩ => ⟨mi, xb, s, ⟨h, f, k, so.mask⟩, so, hR⟩
  · obtain ⟨mi₁, h₁⟩ := H₁
    obtain ⟨mi₂, h₂⟩ := H₂
    have ⟨xb₁, σ₁, g₁, so₁, _⟩ := h₁
    have ⟨xb₂, σ₂, g₂, so₂, _⟩ := h₂
    have : 64 ≤ p.k := g₁.1.k1
    obtain rfl := so_minv so₁ so₂ g₁.1.odd (show 1 ≤ ((p.k + 7) / 8) by show 1 ≤ (p.k + 7) / 8; omega)
    exact ⟨(p, mi₁), h₁, h₂⟩

/-- `rest`'s public data with `-m⁻¹`. -/
abbrev DPub.L (q : VG.Proof.Bignum.X86_64.DPub × BitVec 64) : Lay := ⟨q.1.B, q.1.Z, ((q.1.k + 7) / 8), q.2⟩

/-- After `X := input R`. -/
def DB (q : VG.Proof.Bignum.X86_64.DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, VG.Proof.Bignum.X86_64.DG q.1 xb σ t ∧ VG.Proof.Bignum.X86_64.Good t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 ∧ wv t.mem q.1.B (VG.Proof.Bignum.X86_64.slot ((q.1.k + 7) / 8) aN) ((q.1.k + 7) / 8) = q.1.N ∧
    ((VG.Proof.Bignum.X86_64.word t.mem q.1.B (VG.Proof.Bignum.X86_64.slot ((q.1.k + 7) / 8) aN)).toNat * q.2.toNat + 1) % 2 ^ 64 = 0 ∧
    wv t.mem q.1.B (VG.Proof.Bignum.X86_64.slot ((q.1.k + 7) / 8) aXm) ((q.1.k + 7) / 8) < q.1.N ∧ wv t.mem q.1.B (VG.Proof.Bignum.X86_64.slot ((q.1.k + 7) / 8) aOne) ((q.1.k + 7) / 8) = 1

theorem arrays_pdAll {B : Addr} {w : Nat} {m m' : Mem} (h : Arrays B w [aAcc, aTmp, aXm] m m') :
    Frm B (pdAll w) m m' :=
  Frm.of_arrays h (by simp [pdAll, pExpRanges, pBitRanges, bitRanges])

/-- `X := input R` leaks the same in runs with the same public data. -/
theorem pdMm_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.DA) (M.mm aXm aX aR2) (Two VG.Proof.Bignum.X86_64.DB) := by
  refine two_post (two_map DPub.L (fun _ _ ⟨_, σ, g, so, _⟩ => ⟨so.good, g.1.z⟩)
    (M.ctL (by unfold MmUse; decide))) ?_
  rintro q t ⟨xb, σ, g, so, hR⟩
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hn : q.1.B.toNat + VG.Proof.Bignum.X86_64.slot ((q.1.k + 7) / 8) 8 ≤ 2 ^ 64 := by have := g.1.scr.nowrap; have := g.1.z; omega
  refine WP.mono (mmN_ok M (o := aXm) (a := aX) (b := aR2) so.good g.1.z (by omega)
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) so.n so.inv (by rw [hR]; exact g.1.rlt)) fun t' ⟨hg, hn', hinv, hlt, _, ha, k⟩ =>
    ⟨xb, σ, g.step (VG.Proof.Bignum.X86_64.arrays_pdAll ha) k (ha.hslot (by decide)), hg, hn', hinv, hlt, ?_⟩
  rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact so.one

/-- The exponentiation's public data. -/
def DPub.E (q : VG.Proof.Bignum.X86_64.DPub × BitVec 64) : EPub := ⟨DPub.L q, q.1.N, q.1.ep, q.1.len, q.1.eb⟩

theorem db_pre {q : VG.Proof.Bignum.X86_64.DPub × BitVec 64} {t : State} (h : VG.Proof.Bignum.X86_64.DB q t) : VG.Proof.Bignum.X86_64.PExpPre (DPub.E q) t := by
  obtain ⟨xb, σ, g, hg, hn, hinv, hlt, -⟩ := h
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hL2 := g.1.L2
  have hR := VG.Proof.Bignum.coprime_pow2 g.1.odd (64 * ((q.1.k + 7) / 8))
  obtain ⟨x, hx⟩ := VG.Proof.Bignum.X86_64.exists_mont hR g.1.n1 (wv t.mem q.1.B (VG.Proof.Bignum.X86_64.slot ((q.1.k + 7) / 8) aXm) ((q.1.k + 7) / 8))
  have he := g.1.e.congrK g.inScr g.2.2.1
  exact ⟨_, x, ⟨hg, hn, hinv, rfl⟩, ⟨g.1.z, show 2 ≤ ((q.1.k + 7) / 8) by omega,
    show ((q.1.k + 7) / 8) < 2 ^ 31 by omega, hR, hlt, hx⟩,
    (g.fixed sE (by decide)).trans g.1.hE, (g.fixed sElen (by decide)).trans g.1.hL, g.1.L1,
    src_esrc he g.1.el (show q.1.len < 2 ^ 31 by omega)⟩

/-- After the exponentiation. -/
def DC (q : VG.Proof.Bignum.X86_64.DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ X x, VG.Proof.Bignum.X86_64.DG q.1 xb σ t ∧ ExpCtx t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 q.1.N X ∧
    YSt t.mem q.1.B ((q.1.k + 7) / 8) q.1.N x (Spec.Rsa.os2ip q.1.eb) ∧ wv t.mem q.1.B (VG.Proof.Bignum.X86_64.slot ((q.1.k + 7) / 8) aOne) ((q.1.k + 7) / 8) = 1

theorem pExpRanges_pdAll (w : Nat) : ∀ r ∈ pExpRanges w, r ∈ pdAll w :=
  fun _ hr => List.mem_append_right _ hr

/-- The exponentiation leaks the same in runs that agree on `e`. -/
theorem pdExp_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.DB) (Precomputed.expLoop M.mm) (Two VG.Proof.Bignum.X86_64.DC) := by
  refine two_post ((two_map DPub.E (fun _ _ h => VG.Proof.Bignum.X86_64.db_pre h) VG.Proof.Bignum.X86_64.pExpLoop_ct).mono (fun _ _ h => h)
    fun _ _ _ => trivial) ?_
  rintro q t h
  obtain ⟨X, x, hc, hf, he, hlen, hL1, hsrc⟩ := VG.Proof.Bignum.X86_64.db_pre h
  obtain ⟨xb, σ, g, -, -, -, -, hone⟩ := h
  have hn : q.1.B.toNat + VG.Proof.Bignum.X86_64.slot ((q.1.k + 7) / 8) 8 ≤ 2 ^ 64 := by have := g.1.scr.nowrap; have := g.1.z; omega
  refine WP.mono (pExpLoop_ok hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 he hlen hsrc.1 hL1
    hsrc.2.1 hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2) fun t' ⟨hc', hy, f₀, k⟩ => ?_
  have f : Frm q.1.B (pExpRanges ((q.1.k + 7) / 8)) t.mem t'.mem := f₀
  refine ⟨xb, σ, X, x, g.step (f.mono (VG.Proof.Bignum.X86_64.pExpRanges_pdAll _)) k
      (f.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (by unfold sMask sFn; omega)), hc', hy, ?_⟩
  rw [f.wv_eq (fun r hr => by
      have := hdr_lt_slot ((q.1.k + 7) / 8) aOne (show 31 < 32 by decide)
      have := VG.Proof.Bignum.X86_64.slot_sep (w := ((q.1.k + 7) / 8)) (show aOne ≠ aAcc by decide)
      have := VG.Proof.Bignum.X86_64.slot_sep (w := ((q.1.k + 7) / 8)) (show aOne ≠ aTmp by decide)
      have := VG.Proof.Bignum.X86_64.slot_sep (w := ((q.1.k + 7) / 8)) (show aOne ≠ aY by decide)
      simp only [pExpRanges, pBitRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [VG.Impl.Bignum.X86_64.Public.sI, VG.Impl.Bignum.X86_64.Public.sV, VG.Impl.Bignum.X86_64.Public.sBit, Precomputed.sStarted, sFn] at * <;> omega)
      (by have := slot_le (w := ((q.1.k + 7) / 8)) (show aOne < 8 by decide); omega)]
  exact hone

/-- After `finish`. -/
def DD (q : VG.Proof.Bignum.X86_64.DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, VG.Proof.Bignum.X86_64.DG q.1 xb σ t ∧ VG.Proof.Bignum.X86_64.Good t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2

/-- `finish` leaks the same in runs that agree on `e`. -/
theorem pdFinish_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.DC) (Precomputed.finish M.mm) (Two VG.Proof.Bignum.X86_64.DD) := by
  refine two_post (two_map (fun q => (⟨DPub.L q, q.1.N, Spec.Rsa.os2ip q.1.eb⟩ : VG.Proof.Bignum.X86_64.FPub))
    (fun q _ ⟨_, _, X, x, g, hc, hy, _⟩ => ⟨X, x, hc, hy, g.1.z, show 2 ≤ (q.1.k + 7) / 8 by have := g.1.k1; omega,
      show (q.1.k + 7) / 8 < 2 ^ 31 by have := g.1.k2; omega⟩) VG.Proof.Bignum.X86_64.finish_ct) ?_
  rintro q t ⟨xb, σ, X, x, g, hc, hy, hone⟩
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hR := VG.Proof.Bignum.coprime_pow2 g.1.odd (64 * ((q.1.k + 7) / 8))
  refine WP.mono (pFinish_ok hc g.1.z (by omega) (by omega) hR g.1.n1 hone hy)
    fun t' ⟨hg, _, f, k⟩ => ⟨xb, σ, g.step (f.mono (by simp [finRanges, pdAll, pExpRanges, pBitRanges, bitRanges])) k
      (f.word_eq (fun r hr => by
        have := hdr_lt_slot ((q.1.k + 7) / 8) aAcc (show sMask < 32 by decide)
        have := hdr_lt_slot ((q.1.k + 7) / 8) aTmp (show sMask < 32 by decide)
        have := hdr_lt_slot ((q.1.k + 7) / 8) aY (show sMask < 32 by decide)
        simp only [finRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> omega) (by unfold sMask sFn; omega)), hg⟩

theorem dd_oPre {q : VG.Proof.Bignum.X86_64.DPub × BitVec 64} {t : State} (h : VG.Proof.Bignum.X86_64.DD q t) : OPre ⟨DPub.L q, q.1.k, q.1.op⟩ t := by
  obtain ⟨xb, σ, g, hg⟩ := h
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  exact ⟨_, hg, rfl, g.1.z, show 1 ≤ q.1.k by omega, show q.1.k < 2 ^ 31 by omega, by rw [g.fixed sOut (by decide)]; exact g.1.hO,
    by rw [g.fixed sK (by decide)]; exact g.1.hK, g.2.2.2, fun j hj => by rw [g.2.2.1.2.2]; exact g.1.out j hj,
    g.1.outSep⟩

/-- `rest` leaks the same in runs with the same public data and `e`. -/
theorem pdRest_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.DRel) (Precomputed.rest M.mm) fun _ _ => True := by
  rw [pdRest_eq]
  refine RelCT.seqs_append (by simp [pdIn]) (by simp [pdExp]) (RelCT.seq VG.Proof.Bignum.X86_64.pdSetup_ct ?_)
  refine RelCT.seqs_append (by simp [pdExp]) (by simp [outSteps, outStepsArr]) (RelCT.seq (R := Two VG.Proof.Bignum.X86_64.DD) ?_ ?_)
  · exact RelCT.seq VG.Proof.Bignum.X86_64.pdMm_ct (RelCT.seq VG.Proof.Bignum.X86_64.pdExp_ct VG.Proof.Bignum.X86_64.pdFinish_ct)
  · exact two_map (fun q => (⟨DPub.L q, q.1.k, q.1.op⟩ : OPub)) (fun _ _ h => VG.Proof.Bignum.X86_64.dd_oPre h) out_ct

/-! ## The load and the checks -/

/-- The public data of `vg_rsa_public_precomputed`: `rest`'s, `pre` and the
stack pointer. -/
structure CPubD where
  d : VG.Proof.Bignum.X86_64.DPub
  pp : Addr
  rsp : Addr

/-- What the load keeps. -/
def LH (p : VG.Proof.Bignum.X86_64.CPubD) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.Scr t p.d.B p.d.Z ∧ t.gpr .rdi = p.d.B ∧ VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) 8 ≤ p.d.Z ∧ 64 ≤ p.d.k ∧ p.d.k ≤ 1024 ∧
    VG.Proof.Bignum.X86_64.word t.mem p.d.B (8 * sK) = BitVec.ofNat 64 p.d.k ∧ VG.Proof.Bignum.X86_64.word t.mem p.d.B (8 * sN) = p.pp ∧
    (∀ i < 2 * ((p.d.k + 7) / 8), InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off p.pp (8 * i)) 8) ∧
    (∀ j < 16 * ((p.d.k + 7) / 8), p.d.Z ≤ VG.Proof.Bignum.X86_64.ofs p.d.B (p.pp + BitVec.ofNat 64 j))

theorem LH.congr {p : VG.Proof.Bignum.X86_64.CPubD} {s t : State} (h : VG.Proof.Bignum.X86_64.LH p s) {rs : List (Nat × Nat)} (hf : Frm p.d.B rs s.mem t.mem)
    (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs) : VG.Proof.Bignum.X86_64.LH p t := by
  obtain ⟨hs, hdi, hZ, hk1, hk2, hK, hN, hpr, hps⟩ := h
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, hZ, hk1, hk2, (hfx sK (by decide)).trans hK,
    (hfx sN (by decide)).trans hN, fun i hi => by rw [k.2.1, k.2.2]; exact hpr i hi, hps⟩

theorem pins_LH : Pins VG.Proof.Bignum.X86_64.LH [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- `LH` with the header's `w` and bases. -/
def LW (p : VG.Proof.Bignum.X86_64.CPubD) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.LH p t ∧ VG.Proof.Bignum.X86_64.word t.mem p.d.B (8 * sW) = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
    (∀ j < 8, VG.Proof.Bignum.X86_64.word t.mem p.d.B (8 * sArr j) = VG.Proof.Bignum.X86_64.off p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) j))

/-- A copy of `w` words from `pre + 8 c` into array `j`. -/
theorem ldCopy_ok {p : VG.Proof.Bignum.X86_64.CPubD} {t : State} (h : VG.Proof.Bignum.X86_64.LW p t) {c j : Nat} (hc : c ≤ (p.d.k + 7) / 8) (hj : j < 8)
    (hsi : t.gpr .rsi = VG.Proof.Bignum.X86_64.off p.pp (8 * c)) (hbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) j))
    (h12 : t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) :
    WP isa copyWords t fun t' => VG.Proof.Bignum.X86_64.LW p t' ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .r14] t t' := by
  have h₀ : VG.Proof.Bignum.X86_64.LH p t := h.1
  obtain ⟨⟨hs, hdi, hZ, hk1, hk2, hK, hN, hpr, hps⟩, hW, hb⟩ := h
  have hn := hs.nowrap
  have hsl := slot_le (w := (p.d.k + 7) / 8) hj
  have hge := hdr_lt_slot ((p.d.k + 7) / 8) j (show 31 < 32 by decide)
  have hA : ∀ i < 8, 8 * sArr i + 8 ≤ VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) j := fun i hi => by unfold sArr; omega
  refine WP.mono (copyWords_ok (S := p.pp) (eS := 8 * c) hsi hbx h12 (by omega) (by omega) (by omega)
    (fun i hi => by rw [show 8 * c + 8 * i = 8 * (c + i) by omega]; exact hpr _ (by omega))
    (fun i hi => hs.st (by omega))
    (fun i hi b hb => Or.inr (by
      have := hps (8 * c + 8 * i + b) (by omega)
      rw [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; omega))) fun t' ⟨_, _, ho, k⟩ => ?_
  refine ⟨⟨h₀.congr (Frm.of_outside ho (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; left; omega) k (by decide),
    by rw [ho.word (by unfold sW; omega) (by unfold sW; omega)]; exact hW,
    fun i hi => by rw [ho.word (d := 8 * sArr i) (Or.inl (hA i hi)) (by unfold sArr; omega)]; exact hb i hi⟩, k⟩

/-- The load and the checks leak the same in runs with the same public data. -/
theorem pdLoad_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.LH) (seqs Precomputed.load) fun _ _ => True := by
  unfold Precomputed.load
  -- `w`, the bases, and the first copy's registers.
  refine RelCT.seq (two_piece (Ψ := fun p t => VG.Proof.Bignum.X86_64.LW p t ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off p.pp (8 * 0) ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) aN) ∧ t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) _
    VG.Proof.Bignum.X86_64.pins_LH (by taint_decide) ?_) ?_
  · intro p t h
    have h' := h
    obtain ⟨hs, hdi, hZ, hk1, hk2, hK, hN, -⟩ := h'
    obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
    refine WP.mono (setupHead_ok hs hdi hZ (by omega) hK hN) fun t' ⟨h12, _, hsi, hbx, hW, hb, hf, k⟩ =>
      ⟨⟨h.congr hf (fun r hr => ?_) k (by decide), hW, hb⟩, by rw [hsi]; simp [VG.Proof.Bignum.X86_64.off], hbx, h12⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
  -- `m`.
  refine RelCT.seq (two_piece (Ψ := fun p t => VG.Proof.Bignum.X86_64.LW p t ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off p.pp (8 * 0) ∧
      t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.rsi, .rbx, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hsi, hbx, h12⟩
    exact WP.mono (VG.Proof.Bignum.X86_64.ldCopy_ok h (Nat.zero_le _) (by decide) hsi hbx h12) fun t' ⟨h', k⟩ =>
      ⟨h', (k.gpr (by decide)).trans hsi, (k.gpr (by decide)).trans h12⟩
  -- `R² mod m`'s registers.
  refine RelCT.seq (two_piece (Ψ := fun p t => VG.Proof.Bignum.X86_64.LW p t ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off p.pp (8 * ((p.d.k + 7) / 8)) ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) aR2) ∧ t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8))
    [.rdi, .rsi, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.1.2.1, h₂.1.1.2.1]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hsi, h12⟩
    have hs := h.1.1
    have hn := hs.nowrap
    have hZ := h.1.2.2.1
    obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
    have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 ((p.d.k + 7) / 8) → r + r + (r + r) + (r + r + (r + r)) =
        BitVec.ofNat 64 (8 * ((p.d.k + 7) / 8)) := by
      rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega
    have hsi' : t.gpr .rsi = p.pp := by rw [hsi]; simp [VG.Proof.Bignum.X86_64.off]
    refine WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t' => t'.gpr .rsi = VG.Proof.Bignum.X86_64.off p.pp (8 * ((p.d.k + 7) / 8)) ∧
        t'.gpr .rbx = VG.Proof.Bignum.X86_64.off p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) aR2) ∧ t'.mem = t.mem) (by
      unfold eightW
      simp only [List.cons_append, List.nil_append]
      xrun [State.ea, hdr, h.1.2.1, hdrOff, hs.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega),
        h.2.2 aR2 (by decide), h12, hsi', hax8 _ rfl]) rfl)
      fun t' ⟨⟨hsi₁, hbx₁, hm⟩, k⟩ => ⟨⟨h.1.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k
        (by decide), by rw [hm]; exact h.2.1, fun j hj => by rw [hm]; exact h.2.2 j hj⟩, hsi₁, hbx₁,
        (k.gpr (by decide)).trans h12⟩
  -- `R² mod m`.
  refine RelCT.seq (two_piece (Ψ := fun p t => VG.Proof.Bignum.X86_64.LW p t ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) aR2) ∧
      t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.rsi, .rbx, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hsi, hbx, h12⟩
    exact WP.mono (VG.Proof.Bignum.X86_64.ldCopy_ok h (Nat.le_refl _) (by decide) hsi hbx h12) fun t' ⟨h', k⟩ =>
      ⟨h', (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h12⟩
  -- The comparison's registers.
  refine RelCT.seq (two_piece (Ψ := fun p t => VG.Proof.Bignum.X86_64.LH p t ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) aR2) ∧
      t.gpr .r10 = VG.Proof.Bignum.X86_64.off p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) aN) ∧ t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false) [.rdi] (fun p s₁ s₂ h₁ h₂ => VG.Proof.Bignum.X86_64.pins_LH p s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hbx, h12⟩
    have hs := h.1.1
    have hn := hs.nowrap
    have hZ := h.1.2.2.1
    obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
    refine WP.mono (WP.keep [.r10, .rbp] (Q := fun t' => t'.gpr .r10 = VG.Proof.Bignum.X86_64.off p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) aN) ∧
        t'.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t'.mem = t.mem) (by
      xrun [State.ea, hdr, h.1.2.1, hdrOff, hs.ld (d := 8 * sArr aN) (by unfold sArr aN; omega),
        h.2.2 aN (by decide)]) rfl)
      fun t' ⟨⟨h10, hbp, hm⟩, k⟩ => ⟨h.1.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k
        (by decide), (k.gpr (by decide)).trans hbx, h10, (k.gpr (by decide)).trans h12, hbp⟩
  -- The comparison.
  refine RelCT.seq (two_piece (Ψ := fun (p : VG.Proof.Bignum.X86_64.CPubD) t => t.gpr .r10 = VG.Proof.Bignum.X86_64.off p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.rbx, .r10, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hbx, h10, h12, hbp⟩
    have hZ := h.2.2.1
    have hk1 := h.2.2.2.1
    have hk2 := h.2.2.2.2.1
    exact WP.mono (cmpLoop_ok h.1 hbx h10 h12 hbp (by omega) (by omega)
      (by have := slot_le (w := (p.d.k + 7) / 8) (show aR2 < 8 by decide); omega)
      (by have := slot_le (w := (p.d.k + 7) / 8) (show aN < 8 by decide); omega)) fun t' ⟨_, _, k⟩ =>
      ⟨(k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- The checks.
  exact two_taint [.r10, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1, h₂.1]
    · rw [h₁.2, h₂.2]) (by taint_decide)

/-! ## The whole function -/

/-- A state the contract allows, with the public data `p`. -/
def CR (p : VG.Proof.Bignum.X86_64.CPubD) (s : State) : Prop :=
  pdContract.pre s ∧ s.gpr .rsp = p.rsp ∧ stackArg s 2 = p.d.B ∧ (stackArg s 3).toNat * 8 = p.d.Z ∧
    (s.gpr .rsi).toNat = p.d.k ∧ s.gpr .rdi = p.d.op ∧ s.gpr .rdx = p.pp ∧ s.gpr .r8 = p.d.ep ∧
    stackArg s 0 = p.d.ip ∧ (s.gpr .r9).toNat = p.d.len ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = p.d.eb ∧
    wv s.mem (s.gpr .rdx) 0 (((s.gpr .rsi).toNat + 7) / 8) = p.d.N ∧
    wv s.mem (s.gpr .rdx) (8 * (((s.gpr .rsi).toNat + 7) / 8)) (((s.gpr .rsi).toNat + 7) / 8) = p.d.R

/-- What `entry` leaves (`pdEntry_ok`). -/
def PdEnt (s t : State) : Prop :=
  t.gpr .rdi = stackArg s 2 ∧
    VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * 0) = s.gpr .rbx ∧ VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * 1) = s.gpr .rbp ∧
    VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * 2) = s.gpr .r12 ∧ VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * 3) = s.gpr .r13 ∧
    VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * 4) = s.gpr .r14 ∧ VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * 5) = s.gpr .r15 ∧
    VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sN) = s.gpr .rdx ∧
    VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sK) = s.gpr .rsi ∧ VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sE) = s.gpr .r8 ∧
    VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sElen) = s.gpr .r9 ∧ VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sIn) = stackArg s 0 ∧
    VG.Proof.Bignum.X86_64.Outside (stackArg s 2) 0 (8 * 22) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r11, .rax, .rdi] s t

theorem pdEntry_split : Precomputed.entry =
    ([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++ Precomputed.entry.drop 1 := rfl

/-- After `entry`'s first instruction. -/
def CE1 (p : VG.Proof.Bignum.X86_64.CPubD) (t : State) : Prop :=
  ∃ s, VG.Proof.Bignum.X86_64.CR p s ∧ t.gpr .r11 = p.d.B ∧ t.gpr .rsp = p.rsp ∧ WP isa (.block (Precomputed.entry.drop 1)) t (VG.Proof.Bignum.X86_64.PdEnt s)

/-- After `entry`. -/
def CE2 (p : VG.Proof.Bignum.X86_64.CPubD) (t : State) : Prop := ∃ s, VG.Proof.Bignum.X86_64.CR p s ∧ VG.Proof.Bignum.X86_64.PdEnt s t

/-- After the load and the checks (`pdLoad_ok`). -/
def CL (p : VG.Proof.Bignum.X86_64.CPubD) (t : State) : Prop :=
  ∃ s t₁, VG.Proof.Bignum.X86_64.CR p s ∧ VG.Proof.Bignum.X86_64.PdEnt s t₁ ∧
    wv t.mem p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) aN) ((p.d.k + 7) / 8) = p.d.N ∧
    wv t.mem p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) aR2) ((p.d.k + 7) / 8) = p.d.R ∧
    VG.Proof.Bignum.X86_64.word t.mem p.d.B (8 * sW) = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
    (∀ j < 8, VG.Proof.Bignum.X86_64.word t.mem p.d.B (8 * sArr j) = VG.Proof.Bignum.X86_64.off p.d.B (VG.Proof.Bignum.X86_64.slot ((p.d.k + 7) / 8) j)) ∧
    t.zf = some (!(VG.Proof.Bignum.X86_64.chkv ((p.d.k + 7) / 8) p.d.N p.d.R)) ∧
    Frm p.d.B (pdLoadRanges ((p.d.k + 7) / 8)) t₁.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t₁ t

theorem ce2_lh {p : VG.Proof.Bignum.X86_64.CPubD} {t : State} (h : VG.Proof.Bignum.X86_64.CE2 p t) : VG.Proof.Bignum.X86_64.LH p t := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, -, hpp, -⟩, hdi, -, -, -, -, -, -, -, hN, hK, -, -, -, -, k⟩ := h
  have c := VG.Proof.Bignum.X86_64.pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  subst hB hZ hk hpp
  exact ⟨c.hs.congr k.2.2, hdi, by dsimp only; unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega, c.hk1, c.hk2, by rw [hK, VG.Proof.Bignum.X86_64.ofNat_toNat64], hN,
    fun i hi => by rw [k.2.1, k.2.2]; exact c.hpr i hi, c.hps⟩

/-- The load's post, from `entry`'s. -/
theorem ce2_load {p : VG.Proof.Bignum.X86_64.CPubD} {t : State} (h : VG.Proof.Bignum.X86_64.CE2 p t) : WP isa (seqs Precomputed.load) t (VG.Proof.Bignum.X86_64.CL p) := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, hs, he⟩ := h
  have hs' := hs
  have he' := he
  obtain ⟨hdi, -, -, -, -, -, -, -, hN, hK, -, -, -, ho₁, k₁⟩ := he'
  obtain ⟨hpre, -, hB, hZ, hk, -, hpp, -, -, -, -, hNv, hRv⟩ := hs
  have c := VG.Proof.Bignum.X86_64.pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  have hn := c.hs.nowrap
  have i₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem := InScr.of_outside ho₁ (by omega)
  have hz : VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  refine WP.mono (pdLoad_ok (c.hs.congr k₁.2.2) hdi hz (by omega) (by omega) (by rw [hK, VG.Proof.Bignum.X86_64.ofNat_toNat64])
    hN (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact c.hpr i hi) c.hps) fun t' ⟨hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩ => ?_
  rw [VG.Proof.Bignum.X86_64.pre_wv_entry c i₁ (by omega), hNv] at hN₂
  rw [VG.Proof.Bignum.X86_64.pre_wv_entry c i₁ (by omega), hRv] at hR₂
  rw [VG.Proof.Bignum.X86_64.chk_eq (by omega), hN₂, hR₂] at hz₂
  subst hB hZ hk hpp
  exact ⟨s, t, hs', he, hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩

/-- What `fail` needs after the load. -/
theorem cl_fail {p : VG.Proof.Bignum.X86_64.CPubD} {t : State} (h : VG.Proof.Bignum.X86_64.CL p t) :
    VG.Proof.Bignum.X86_64.Scr t p.d.B p.d.Z ∧ t.gpr .rdi = p.d.B ∧ 8 * 32 ≤ p.d.Z ∧ 64 ≤ p.d.k ∧ p.d.k ≤ 1024 ∧
      VG.Proof.Bignum.X86_64.word t.mem p.d.B (8 * sOut) = p.d.op ∧ VG.Proof.Bignum.X86_64.word t.mem p.d.B (8 * sK) = BitVec.ofNat 64 p.d.k := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, t₁, ⟨hpre, -, hB, hZ, hk, hop, -⟩, ⟨hdi, -, -, -, -, -, -, hO, -, hK, -, -, -, -, k₁⟩, -, -, -, -, -,
    f, k⟩ := h
  have c := VG.Proof.Bignum.X86_64.pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  subst hB hZ hk hop
  have x := Fixed.of_frm f (pdLoadRanges_fixed _)
  exact ⟨c.hs.congr (k₁.trans k).2.2, (k.gpr (by decide)).trans hdi, by dsimp only; omega, c.hk1, c.hk2,
    (x sOut (by decide)).trans hO, by rw [x sK (by decide), hK, VG.Proof.Bignum.X86_64.ofNat_toNat64]⟩

/-- `rest`'s hypotheses after the load, for values that pass the checks. -/
theorem cl_rest {p : VG.Proof.Bignum.X86_64.CPubD} {t : State} (h : VG.Proof.Bignum.X86_64.CL p t) (he : isa.eval .e t = some false) : VG.Proof.Bignum.X86_64.DRel p.d t := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, t₁, ⟨hpre, -, hB, hZ, hk, hop, hpp, hep, hip, hlen, heb, hNv, hRv⟩,
    ⟨hdi, -, -, -, -, -, -, hO, -, hK, hE, hL, hIn, ho₁, k₁⟩, hN, hR, hW, hb, hz, f, k₂⟩ := h
  have c := VG.Proof.Bignum.X86_64.pdCtx_of hpre
  have := c.hk1
  subst hB hZ hk hop hpp hep hip hlen heb hNv hRv
  have hchk : VG.Proof.Bignum.X86_64.chkv (((s.gpr .rsi).toNat + 7) / 8)
      (wv t.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8))
      (wv t.mem (stackArg s 2) (VG.Proof.Bignum.X86_64.slot (((s.gpr .rsi).toNat + 7) / 8) aR2) (((s.gpr .rsi).toNat + 7) / 8)) = true := by
    rw [hN, hR]; simp only [VG.X86_64.eval, hz, Option.some.injEq] at he; simpa using he
  rw [← VG.Proof.Bignum.X86_64.chk_eq (by omega)] at hchk
  obtain ⟨hodd, hN1, hRN⟩ := VG.Proof.Bignum.X86_64.checks_facts (by omega) hchk
  have hp := VG.Proof.Bignum.X86_64.pdPre_of c hdi hO hK hE hL hIn ho₁ k₁ hW hb f k₂ hodd hN1 hRN
  rw [hN, hR] at hp
  exact ⟨_, hp⟩

/-- `vg_rsa_public_precomputed` leaks the same in runs that agree on the public
data. -/
theorem pdCode_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.CR) (Precomputed.code M.mm) fun _ _ => True := by
  unfold Precomputed.code
  refine RelCT.seq (R := Two VG.Proof.Bignum.X86_64.CE2) ?_ ?_
  · rw [VG.Proof.Bignum.X86_64.pdEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.CE1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := VG.Proof.Bignum.X86_64.pdCtx_of hs.1
    have hZ := c.hZ
    have hk1 := c.hk1
    have hw : ∀ i < 22, InRegions s.wr (VG.Proof.Bignum.X86_64.off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++
        Precomputed.entry.drop 1)) s (VG.Proof.Bignum.X86_64.PdEnt s) := by
      rw [← VG.Proof.Bignum.X86_64.pdEntry_split]; exact VG.Proof.Bignum.X86_64.pdEntry_ok rfl hw c.ha0 c.ha2 c.hsep
    have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
    have hB' : s.mem.readW (stackArgAddr s 2) 64 = stackArg s 2 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 2)
      (by xrun [State.ea, e2, c.ha2, hB']) rfl)) fun t ⟨hw', h11, k⟩ =>
        ⟨s, hs, h11.trans hs.2.2.1, (k.gpr (by decide)).trans hs.2.1, hw'⟩
  refine RelCT.seq (R := Two VG.Proof.Bignum.X86_64.CL) (two_post (pdLoad_ct.mono (fun _ _ h => two_mono (fun _ _ h => VG.Proof.Bignum.X86_64.ce2_lh h) h)
    fun _ _ h => h) fun p t h => VG.Proof.Bignum.X86_64.ce2_load h) ?_
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, _, z₁, _⟩ ⟨_, _, _, _, _, _, _, _, z₂, _⟩ => by
    simp only [VG.X86_64.eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold fail
    refine RelCT.seq (two_piece (Ψ := fun (p : VG.Proof.Bignum.X86_64.CPubD) t => t.gpr .rsi = p.d.op ∧
        t.gpr .rcx = BitVec.ofNat 64 p.d.k ∧ t.gpr .rdi = p.d.B) [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(VG.Proof.Bignum.X86_64.cl_fail h₁.1).2.1, (VG.Proof.Bignum.X86_64.cl_fail h₂.1).2.1])
      (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨hs, hdi, hZ, hk1, hk2, hO, hK⟩ := VG.Proof.Bignum.X86_64.cl_fail h
    have hn := hs.nowrap
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off p.d.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = p.d.op ∧
        t'.gpr .rcx = BitVec.ofNat 64 p.d.k) (by
      xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hl sK (by decide), hO, hK]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨hsi, hcx, (k'.gpr (by decide)).trans hdi⟩
  · -- `rest`.
    exact two_map (fun p => p.d) (fun _ _ h => VG.Proof.Bignum.X86_64.cl_rest h.1 h.2) VG.Proof.Bignum.X86_64.pdRest_ct

/-- `wordsAt`'s words determine the numbers they make. -/
theorem wv_of_wordsAt {m m' : Mem} {p : Addr} {n c w : Nat}
    (h : Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt m' p n) (hc : c + w ≤ n) :
    wv m p (8 * c) w = wv m' p (8 * c) w :=
  wv_congr fun i hi => by
    have := congrArg (fun l => l[c + i]?) h
    simp only [Spec.Rsa.wordsAt, List.getElem?_map, List.getElem?_range (show c + i < n by omega),
      Option.map_some, Option.some.injEq] at this
    show m.readW (p + BitVec.ofNat 64 (8 * c + 8 * i)) 64 = m'.readW (p + BitVec.ofNat 64 (8 * c + 8 * i)) 64
    rw [show 8 * c + 8 * i = 8 * (c + i) by omega]
    exact this

/-- The public data of a state. -/
def cpubOfD (s : State) : VG.Proof.Bignum.X86_64.CPubD :=
  ⟨⟨stackArg s 2, (stackArg s 3).toNat * 8, (s.gpr .rsi).toNat, s.gpr .rdi, s.gpr .r8, stackArg s 0,
    (s.gpr .r9).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat,
    wv s.mem (s.gpr .rdx) 0 (((s.gpr .rsi).toNat + 7) / 8),
    wv s.mem (s.gpr .rdx) (8 * (((s.gpr .rsi).toNat + 7) / 8)) (((s.gpr .rsi).toNat + 7) / 8)⟩,
    s.gpr .rdx, s.gpr .rsp⟩

/-- `vg_rsa_public_precomputed` is constant time but for `pre` and `e`. -/
theorem pdCode_constantTime : ConstantTime isa pdContract.pre pdContract.pub (Precomputed.code M.mm) := by
  refine RelCT.constantTime (pdCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨VG.Proof.Bignum.X86_64.cpubOfD s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, -, a2, a3, hw, he⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    have c := VG.Proof.Bignum.X86_64.pdCtx_of h₂
    have hpl := c.hpl
    rw [r .rcx (by decide), r .rsi (by decide)] at hpl
    rw [r .rdx (by decide), r .rcx (by decide)] at hw
    refine ⟨h₂, r .rsp (by decide), a2.symm, by rw [← a3]; rfl, by rw [r .rsi (by decide)]; rfl, r .rdi (by decide),
      r .rdx (by decide), r .r8 (by decide), a0.symm, by rw [r .r9 (by decide)]; rfl, he.symm, ?_, ?_⟩
    · rw [r .rdx (by decide), r .rsi (by decide), show (0 : Nat) = 8 * 0 from rfl]
      exact (VG.Proof.Bignum.X86_64.wv_of_wordsAt hw (by omega)).symm
    · rw [r .rdx (by decide), r .rsi (by decide)]
      exact (VG.Proof.Bignum.X86_64.wv_of_wordsAt hw (by omega)).symm

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PdVerified`. -/
section

/-!
# `vg_rsa_public_precomputed` on x86-64: verified against the shared contract

`pdContract` states the shared contract on the registers and the stack
(`precomputed_implies`); with correctness (`pdCode_correct`) and constant
time (`pdCode_constantTime`), `Precomputed.code` is verified
(`precomputed_verified`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64

/-- A state meeting `pdContract.pre`: a 512-bit modulus, a one-byte
exponent, and the stack arguments at `0x6008`. -/
def pdSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 16 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else if a = 0x6010 then 0x40 else if a = 0x6019 then 0x80
    else if a = 0x6021 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x6008, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

/-- The leak of `pre` and `e`, as numbers, determines each when `pre`'s
length is the same. -/
theorem leak_eq2 {a c : List (BitVec 64)} {b d : List Byte} (hl : a.length = c.length)
    (h : a.map (·.toNat) ++ b.map (·.toNat) = c.map (·.toNat) ++ d.map (·.toNat)) : a = c ∧ b = d := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hl])
  exact ⟨List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) h1,
    List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) h2⟩

theorem precomputed_implies : pdContract.Implies (Spec.Rsa.publicPrecomputedContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Bignum.X86_64.pdContract, stackArgs_four, List.append_eq] at h
    sig_pre [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Bignum.X86_64.pdContract, stackArgs_four, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Bignum.X86_64.pdContract, stackArgs_four, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Bignum.X86_64.pdContract, stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Bignum.X86_64.pdContract, stackArgs_four, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3⟩ := h
    obtain ⟨hw, he⟩ := VG.Proof.Bignum.X86_64.leak_eq2 (by simp [Spec.Rsa.wordsAt, hcx]) hl
    refine ⟨?_, a0, a1, a2, a3, hw, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Bignum.X86_64.pdContract, stackArgs_four, List.append_eq] [pdSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Bignum.X86_64.pdSatState

/-- `vg_rsa_public_precomputed` with Montgomery multiplication `M`, given
that its code never loads MXCSR (which the registration file evaluates). -/
theorem precomputed_verified (M : Mont)
    (hmx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Precomputed.code M.mm) (Spec.Rsa.publicPrecomputedContract abi) :=
  Verified.of_correct (VG.Proof.Bignum.X86_64.pdCode_correct M hmx) VG.Proof.Bignum.X86_64.pdCode_constantTime VG.Proof.Bignum.X86_64.precomputed_implies

end VG.Proof.Bignum.X86_64

end
