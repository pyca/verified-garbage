module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Frame
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Rsa.X86.Rd.Move

/-! # Prime recovery's stage loops on i686

The loops whose counts are header words written from public sizes: the word
stages `c = 2^k, …, 1` (`RecoverDetRt.wordStagesL`, `4 c` in `sC4`, a stage
run where `4 c` is below a public limit), the bit stages `b = 2^k, …, 2^m`
(`bitStagesL`, `b` in `sB`) and a body run `b` times (`timesH`, counted in
`sBc`). Each takes the invariants of its caller, before and after a stage,
and needs of them only the working space and the header word.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (Keep Ws slot)
open VG.Impl.Rsa.X86.Keys (hdr)

variable {B : Addr} {Z w N : Nat}

/-- A header word read. -/
theorem readHdr {s : State} (h : Ws s B Z w N) {d : Nat} (hd : d + 4 ≤ hdr) :
    readSrc s (.mem (sc d)) = some (BitVec.ofNat 32 (slot s.mem B d)) := by
  have := h.hdr_le
  rw [readSrc_sc h.workspace (by omega)]
  simp only [slot, w32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A header word written from a register. -/
theorem storeHdr {s : State} {is : List Instr} {Q : State → Prop} (h : Ws s B Z w N) {d : Nat}
    (hd : d + 4 ≤ hdr) (r : Reg)
    (k : ∀ t, Keep B w [] [d] s.mem t.mem → slot t.mem B d = (s.gpr r).toNat → Keeps [] s t →
      t.zf = s.zf → t.cf = s.cf → WP isa (.block is) t Q) :
    WP isa (.block (.store (sc d) r :: is)) s Q := by
  have := h.hdr_le
  refine wp_storeS (h.workspace.ea (by omega)) (h.workspace.write (by omega)) fun t T => ?_
  refine k t ?_ (by unfold slot; rw [T.mem, w32_write_self]) (T.keeps []) T.zf T.cf
  rw [T.mem]
  exact Keep.of_slot (writeW32_outside _ _ _ (by unfold hdr at hd; omega)) (by simp)

theorem fupd_keeps {s t : State} (F : Fupd s t) (rs : List Reg) : Keeps rs s t :=
  ⟨fun r _ => by rw [F.gpr], F.rd, F.wr⟩

theorem ofNat_lt_toNat {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

open VG.Impl.Rsa.X86.RecoverDetRt (wordStagesL bitStagesL timesH sC4 sB sBc)

/-- The word stages `c = 2^j` for `j = k, …, 0`: `Pre j` before stage `2^j` (with `4 · 2^j` in
`sC4`), `Post j` after it, the body run where `4 · 2^j < lim`. -/
theorem wordStagesL_ok {k lim : Nat} {limit : List Instr} {body : Prog isa} {s : State}
    {Fin : State → Prop} (Pre Post : Nat → State → Prop)
    (hk : k ≤ 20) (hs : Ws s B Z w N)
    (hinit : ∀ t, Keep B w [] [sC4] s.mem t.mem → slot t.mem B sC4 = 4 * 2 ^ k → Keeps [.eax] s t → Pre k t)
    (hpre : ∀ j t, j ≤ k → Pre j t → Ws t B Z w N ∧ slot t.mem B sC4 = 4 * 2 ^ j)
    (hlimit : ∀ j t, j ≤ k → Pre j t → ∀ (is : List Instr) (Q : State → Prop),
      (∀ u, Keeps opRegs t u → u.mem = t.mem → (u.gpr .eax).toNat = lim → WP isa (.block is) u Q) →
      WP isa (.block (limit ++ is)) t Q)
    (hstable : ∀ j t u, j ≤ k → Pre j t → Keeps opRegs t u → u.mem = t.mem → Pre j u)
    (hbody : ∀ j t, j ≤ k → Pre j t → 4 * 2 ^ j < lim → WP isa body t (Post j))
    (hskip : ∀ j t, j ≤ k → Pre j t → lim ≤ 4 * 2 ^ j → Post j t)
    (hpost : ∀ j t, j ≤ k → Post j t → Ws t B Z w N ∧ slot t.mem B sC4 = 4 * 2 ^ j)
    (hnext : ∀ j t u, j ≤ k → Post j t → Keep B w [] [sC4] t.mem u.mem → slot u.mem B sC4 = 2 * 2 ^ j →
      Keeps opRegs t u → (0 < j → Pre (j - 1) u) ∧ (j = 0 → Fin u)) :
    WP isa (wordStagesL (2 ^ k) limit body) s Fin := by
  have p20 : 2 ^ k ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hk
  unfold wordStagesL
  refine WP.seq (wp_movS (v := BitVec.ofNat 32 (4 * 2 ^ k)) rfl fun s₁ U₁ _ => ?_)
  refine storeHdr (hs.rest U₁.keeps) (by decide) .eax fun s₂ K₂ e₂ k₂ _ _ => WP.block_nil ?_
  have P₂ : Pre k s₂ := hinit s₂ (by rw [U₁.mem] at K₂; exact K₂)
    (by rw [e₂, U₁.gpr, ofNat_lt_toNat (by omega)]) (U₁.keeps.trans (k₂.mono (by simp)))
  refine WP.loop (M := isa) (Q := Fin) (fun n v => n ≤ k ∧ Pre n v) ?_ k s₂ ⟨Nat.le_refl _, P₂⟩
  rintro j v ⟨hj, P⟩
  have pj : 2 ^ j ≤ 2 ^ 20 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hj) p20
  obtain ⟨wv, sv⟩ := hpre j v hj P
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (hlimit j v hj P _ _ fun u₁ K₁ m₁ e₁ => ?_)
  have wu : Ws u₁ B Z w N := wv.rest K₁
  refine wp_movS (readHdr wu (by decide)) fun u₂ U₂ _ => ?_
  refine VG.Proof.Mont.X86.Square.wp_cmpCF (v := u₂.gpr .eax) rfl fun u₃ F₃ c₃ => WP.block_nil ?_
  have Pu : Pre j u₃ := hstable j v u₃ hj P (K₁.trans ((U₂.keeps.mono (by simp)).trans (fupd_keeps F₃ _)))
    (by rw [F₃.mem, U₂.mem, m₁])
  have ecx : (u₂.gpr .ecx).toNat = 4 * 2 ^ j := by
    rw [U₂.gpr, m₁, sv, ofNat_lt_toNat (by omega)]
  have eax : (u₂.gpr .eax).toNat = lim := by rw [U₂.other _ (by decide), e₁]
  rw [ecx, eax] at c₃
  suffices cont : ∀ t, Post j t → WP isa (.block [.mov .eax (.mem (sc sC4)), .shift .shr .eax 1,
      .store (sc sC4) .eax, .alu .cmp .eax (.imm (BitVec.ofNat 32 4))]) t fun s' =>
      (eval .ae s' = some false ∧ Fin s') ∨ (eval .ae s' = some true ∧ ∃ m < j, m ≤ k ∧ Pre m s') from
    WP.seq (WP.ite (decide (4 * 2 ^ j < lim)) c₃
      (fun hb => WP.mono (hbody j u₃ hj Pu (of_decide_eq_true hb)) cont)
      (fun hb => WP.block_nil (cont _ (hskip j u₃ hj Pu (Nat.le_of_not_lt (of_decide_eq_false hb))))))
  intro t Po
  obtain ⟨wt, st⟩ := hpost j t hj Po
  refine wp_movS (readHdr wt (by decide)) fun t₁ T₁ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun t₂ T₂ => ?_
  have e₂ : (t₂.gpr .eax).toNat = 2 * 2 ^ j := by
    rw [T₂.gpr, BitVec.toNat_ushiftRight, T₁.gpr, st, ofNat_lt_toNat (by omega), Nat.shiftRight_eq_div_pow]
    omega
  have w₂ : Ws t₂ B Z w N := wt.rest (T₁.keeps.trans T₂.keeps)
  refine storeHdr w₂ (by decide) .eax fun t₃ K₃ s₃ k₃ _ _ => ?_
  refine VG.Proof.Mont.X86.Square.wp_cmpCF (v := BitVec.ofNat 32 4) rfl fun t₄ F₄ c₄ => WP.block_nil ?_
  have m₂ : t₂.mem = t.mem := by rw [T₂.mem, T₁.mem]
  have N := hnext j t t₄ hj Po (by rw [F₄.mem, ← m₂]; exact K₃) (by rw [F₄.mem, s₃, e₂])
    ((T₁.keeps.mono (by simp)).trans ((T₂.keeps.mono (by simp)).trans ((k₃.mono (by simp)).trans (fupd_keeps F₄ _))))
  rw [k₃.1 .eax (by simp), e₂, ofNat_lt_toNat (by decide)] at c₄
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact .inl ⟨by simp only [eval, c₄]; decide, N.2 rfl⟩
  · refine .inr ⟨?_, j - 1, by omega, by omega, N.1 hj0⟩
    have : ¬ 2 * 2 ^ j < 4 := by
      have := Nat.pow_le_pow_right (n := 2) (by decide) hj0; omega
    simp only [eval, c₄, this, decide_false, Option.map_some, Bool.not_false]

/-- The bit stages `b = 2^j` for `j = k, …, m`: `Pre j` before stage `2^j` (with `2^j` in `sB`),
`Post j` after it. -/
theorem bitStagesL_ok {k m : Nat} {body : Prog isa} {s : State} {Fin : State → Prop}
    (Pre Post : Nat → State → Prop) (hk : k ≤ 20) (hmk : m ≤ k) (hs : Ws s B Z w N)
    (hinit : ∀ t, Keep B w [] [sB] s.mem t.mem → slot t.mem B sB = 2 ^ k → Keeps [.eax] s t → Pre k t)
    (hbody : ∀ j t, m ≤ j → j ≤ k → Pre j t → WP isa body t (Post j))
    (hpost : ∀ j t, m ≤ j → j ≤ k → Post j t → Ws t B Z w N ∧ slot t.mem B sB = 2 ^ j)
    (hnext : ∀ j t u, m ≤ j → j ≤ k → Post j t → Keep B w [] [sB] t.mem u.mem → slot u.mem B sB = 2 ^ j / 2 →
      Keeps opRegs t u → (m < j → Pre (j - 1) u) ∧ (j = m → Fin u)) :
    WP isa (bitStagesL (2 ^ k) (2 ^ m) body) s Fin := by
  have p20 : 2 ^ k ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hk
  unfold bitStagesL
  refine WP.seq (wp_movS (v := BitVec.ofNat 32 (2 ^ k)) rfl fun s₁ U₁ _ => ?_)
  refine storeHdr (hs.rest U₁.keeps) (by decide) .eax fun s₂ K₂ e₂ k₂ _ _ => WP.block_nil ?_
  have P₂ : Pre k s₂ := hinit s₂ (by rw [U₁.mem] at K₂; exact K₂)
    (by rw [e₂, U₁.gpr, ofNat_lt_toNat (by omega)]) (U₁.keeps.trans (k₂.mono (by simp)))
  refine WP.loop (M := isa) (Q := Fin) (fun n v => m ≤ n ∧ n ≤ k ∧ Pre n v) ?_ k s₂ ⟨hmk, Nat.le_refl _, P₂⟩
  rintro j v ⟨hmj, hj, P⟩
  have pj : 2 ^ j ≤ 2 ^ 20 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hj) p20
  have pm : 2 ^ m ≤ 2 ^ 20 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hmk) p20
  refine WP.seq (WP.mono (hbody j v hmj hj P) fun t Po => ?_)
  obtain ⟨wt, st⟩ := hpost j t hmj hj Po
  refine wp_movS (readHdr wt (by decide)) fun t₁ T₁ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun t₂ T₂ => ?_
  have e₂ : (t₂.gpr .eax).toNat = 2 ^ j / 2 := by
    rw [T₂.gpr, BitVec.toNat_ushiftRight, T₁.gpr, st, ofNat_lt_toNat (by omega), Nat.shiftRight_eq_div_pow,
      Nat.pow_one]
  have w₂ : Ws t₂ B Z w N := wt.rest (T₁.keeps.trans T₂.keeps)
  refine storeHdr w₂ (by decide) .eax fun t₃ K₃ s₃ k₃ _ _ => ?_
  refine VG.Proof.Mont.X86.Square.wp_cmpCF (v := BitVec.ofNat 32 (2 ^ m)) rfl fun t₄ F₄ c₄ => WP.block_nil ?_
  have m₂ : t₂.mem = t.mem := by rw [T₂.mem, T₁.mem]
  have Nx := hnext j t t₄ hmj hj Po (by rw [F₄.mem, ← m₂]; exact K₃) (by rw [F₄.mem, s₃, e₂])
    ((T₁.keeps.mono (by simp)).trans ((T₂.keeps.mono (by simp)).trans ((k₃.mono (by simp)).trans (fupd_keeps F₄ _))))
  rw [k₃.1 .eax (by simp), e₂, ofNat_lt_toNat (by omega)] at c₄
  rcases Nat.eq_or_lt_of_le hmj with rfl | hlt
  · have : 2 ^ m / 2 < 2 ^ m := Nat.div_lt_self (Nat.two_pow_pos _) (by decide)
    exact .inl ⟨by simp only [eval, c₄, this, decide_true, Option.map_some, Bool.not_true], Nx.2 rfl⟩
  · refine .inr ⟨?_, j - 1, by omega, by omega, by omega, Nx.1 hlt⟩
    have : ¬ 2 ^ j / 2 < 2 ^ m := by
      have e : 2 ^ j = 2 ^ (j - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
      rw [e, Nat.mul_div_cancel _ (by decide)]
      exact Nat.not_lt.mpr (Nat.pow_le_pow_right (by decide) (by omega))
    simp only [eval, c₄, this, decide_false, Option.map_some, Bool.not_false]

/-- `body` `b ≥ 1` times (`b` in `sB`): `Pre i` before run `i`, `Post i` after it (with `b - i` in
`sBc`). -/
theorem timesH_ok {b : Nat} {body : Prog isa} {s : State} {Fin : State → Prop}
    (Pre Post : Nat → State → Prop) (hb : 0 < b) (hb32 : b < 2 ^ 32) (hs : Ws s B Z w N)
    (hsB : slot s.mem B sB = b)
    (hinit : ∀ t, Keep B w [] [sBc] s.mem t.mem → slot t.mem B sBc = b → Keeps [.eax] s t → Pre 0 t)
    (hbody : ∀ i t, i < b → Pre i t → WP isa body t (Post i))
    (hpost : ∀ i t, i < b → Post i t → Ws t B Z w N ∧ slot t.mem B sBc = b - i)
    (hnext : ∀ i t u, i < b → Post i t → Keep B w [] [sBc] t.mem u.mem → slot u.mem B sBc = b - (i + 1) →
      Keeps opRegs t u → (i + 1 < b → Pre (i + 1) u) ∧ (i + 1 = b → Fin u)) :
    WP isa (timesH body) s Fin := by
  unfold timesH
  refine WP.seq (wp_movS (readHdr hs (by decide)) fun s₁ U₁ _ => ?_)
  refine storeHdr (hs.rest U₁.keeps) (by decide) .eax fun s₂ K₂ e₂ k₂ _ _ => WP.block_nil ?_
  have P₂ : Pre 0 s₂ := hinit s₂ (by rw [U₁.mem] at K₂; exact K₂)
    (by rw [e₂, U₁.gpr, hsB, ofNat_lt_toNat hb32]) (U₁.keeps.trans (k₂.mono (by simp)))
  refine WP.loop (M := isa) (Q := Fin) (fun n v => ∃ i, n = b - i ∧ i < b ∧ Pre i v) ?_ (b - 0) s₂
    ⟨0, rfl, hb, P₂⟩
  rintro n v ⟨i, rfl, hi, P⟩
  refine WP.seq (WP.mono (hbody i v hi P) fun t Po => ?_)
  obtain ⟨wt, st⟩ := hpost i t hi Po
  refine wp_movS (readHdr wt (by decide)) fun t₁ T₁ _ => ?_
  refine VG.Proof.Mont.X86.Rt.wp_subZ (v := BitVec.ofNat 32 1) rfl fun t₂ T₂ z₂ => ?_
  have e₂ : (t₂.gpr .eax).toNat = b - (i + 1) := by
    rw [T₂.gpr, T₁.gpr, st, BitVec.toNat_sub, ofNat_lt_toNat (x := b - i) (by omega), ofNat_lt_toNat (x := 1) (by decide)]
    omega
  have w₂ : Ws t₂ B Z w N := wt.rest (T₁.keeps.trans T₂.keeps)
  refine storeHdr w₂ (by decide) .eax fun t₃ K₃ s₃ k₃ zf₃ _ => WP.block_nil ?_
  have m₂ : t₂.mem = t.mem := by rw [T₂.mem, T₁.mem]
  have Nx := hnext i t t₃ hi Po (by rw [← m₂]; exact K₃) (by rw [s₃, e₂])
    ((T₁.keeps.mono (by simp)).trans ((T₂.keeps.mono (by simp)).trans (k₃.mono (by simp))))
  have zz : (t₁.gpr .eax - BitVec.ofNat 32 1 == 0) = decide (i + 1 = b) := by
    rw [← T₂.gpr]
    by_cases h : i + 1 = b
    · simp only [h, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq; rw [e₂]; simp; omega
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro e; have := congrArg BitVec.toNat e; rw [e₂] at this; simp at this; omega
  rw [zz] at z₂
  by_cases h : i + 1 = b
  · exact .inl ⟨by simp only [eval, zf₃, z₂, h, decide_true, Option.map_some, Bool.not_true], Nx.2 h⟩
  · exact .inr ⟨by simp only [eval, zf₃, z₂, h, decide_false, Option.map_some, Bool.not_false],
      b - (i + 1), by omega, i + 1, rfl, by omega, Nx.1 (by omega)⟩

/-! ## The bit tests -/

/-- `(2^a q + r) ⊕ 2^a q = r` for `r < 2^a`. -/
theorem xor_high {a q r : Nat} (hr : r < 2 ^ a) : (2 ^ a * q + r) ^^^ (2 ^ a * q) = r := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add q hr,
    show 2 ^ a * q = 2 ^ a * q + 0 from rfl, Nat.testBit_two_pow_mul_add q (Nat.two_pow_pos a)]
  split
  · simp
  · rename_i h
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp

/-- `(2^a q + r) ⊕ r = 2^a q` for `r < 2^a`. -/
theorem xor_low {a q r : Nat} (hr : r < 2 ^ a) : (2 ^ a * q + r) ^^^ r = 2 ^ a * q := by
  have e := xor_high (q := q) hr
  calc (2 ^ a * q + r) ^^^ r = (2 ^ a * q + r) ^^^ ((2 ^ a * q + r) ^^^ 2 ^ a * q) := by rw [e]
    _ = 2 ^ a * q := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- `edx` counted down to zero from `b ≥ 1`, one step of `op` each time: what the bit tests'
loops share. -/
theorem countLoop_ok {op : Instr} {s : State} {b : Nat} (f : Nat → Nat) (hb : 0 < b) (hb32 : b < 2 ^ 32)
    (hd : s.gpr .edx = BitVec.ofNat 32 b)
    (hop : ∀ v, WP isa (.block [op]) v fun v' => Keeps [.eax] v v' ∧ v'.mem = v.mem ∧
      (v'.gpr .eax).toNat = f (v.gpr .eax).toNat) :
    WP isa (.loop (.block [op, .alu .sub .edx (.imm 1)]) .ne) s fun t =>
      Keeps [.eax, .edx] s t ∧ t.mem = s.mem ∧ (t.gpr .eax).toNat = f^[b] (s.gpr .eax).toNat := by
  refine WP.loop (M := isa) (fun n v => ∃ i, n = b - i ∧ i < b ∧ Keeps [.eax, .edx] s v ∧ v.mem = s.mem ∧
    v.gpr .edx = BitVec.ofNat 32 (b - i) ∧ (v.gpr .eax).toNat = f^[i] (s.gpr .eax).toNat) ?_ (b - 0) s
    ⟨0, rfl, hb, Keeps.refl _ _, rfl, by rw [hd, Nat.sub_zero], rfl⟩
  rintro n v ⟨i, rfl, hi, K, m, dx, ax⟩
  refine WP.block_append (M := isa) (l₁ := [op]) (WP.mono (hop v) fun v₁ hv => ?_)
  obtain ⟨K₁, m₁, a₁⟩ := hv
  refine VG.Proof.Mont.X86.Rt.wp_subZ (v := BitVec.ofNat 32 1) rfl fun v₂ U₂ z₂ => WP.block_nil ?_
  have d₁ : v₁.gpr .edx = BitVec.ofNat 32 (b - i) := by rw [K₁.1 _ (by simp), dx]
  have e₂ : v₂.gpr .edx = BitVec.ofNat 32 (b - (i + 1)) := by
    rw [U₂.gpr, d₁]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, ofNat_lt_toNat (x := b - i) (by omega), ofNat_lt_toNat (x := 1) (by decide),
      ofNat_lt_toNat (by omega)]
    omega
  have zz : (v₁.gpr .edx - BitVec.ofNat 32 1 == 0) = decide (i + 1 = b) := by
    rw [← U₂.gpr, e₂]
    by_cases h : i + 1 = b
    · simp only [h, decide_true, beq_iff_eq]
      rw [Nat.sub_self]; rfl
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro e; have := congrArg BitVec.toNat e; rw [ofNat_lt_toNat (by omega)] at this; simp at this; omega
  rw [zz] at z₂
  have K₂ : Keeps [.eax, .edx] s v₂ := K.trans ((K₁.mono (by simp)).trans (U₂.keeps.mono (by simp)))
  have m₂ : v₂.mem = s.mem := by rw [U₂.mem, m₁, m]
  have a₂ : (v₂.gpr .eax).toNat = f^[i + 1] (s.gpr .eax).toNat := by
    rw [U₂.other _ (by decide), a₁, ax, Function.iterate_succ_apply']
  by_cases h : i + 1 = b
  · exact .inl ⟨by simp only [eval, z₂, h, decide_true, Option.map_some, Bool.not_true],
      K₂, m₂, by rw [a₂, h]⟩
  · exact .inr ⟨by simp only [eval, z₂, h, decide_false, Option.map_some, Bool.not_false],
      b - (i + 1), by omega, i + 1, rfl, by omega, K₂, m₂, e₂, a₂⟩

theorem iter_half (x : Nat) : ∀ b, (· / 2)^[b] x = x / 2 ^ b
  | 0 => by simp
  | b + 1 => by rw [Function.iterate_succ_apply', iter_half x b, Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem iter_double (x : Nat) : ∀ b, (fun y => y * 2 % 2 ^ 32)^[b] (x % 2 ^ 32) = x * 2 ^ b % 2 ^ 32
  | 0 => by simp
  | b + 1 => by
    rw [Function.iterate_succ_apply', iter_double x b, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_succ]

theorem halfLoop_ok {s : State} {b : Nat} (hb : 0 < b) (hb32 : b < 2 ^ 32) (hd : s.gpr .edx = BitVec.ofNat 32 b) :
    WP isa (.loop (.block [.shift .shr .eax 1, .alu .sub .edx (.imm 1)]) .ne) s fun t =>
      Keeps [.eax, .edx] s t ∧ t.mem = s.mem ∧ (t.gpr .eax).toNat = (s.gpr .eax).toNat / 2 ^ b := by
  refine WP.mono (countLoop_ok (· / 2) hb hb32 hd fun v => ?_) fun t ⟨K, m, e⟩ => ⟨K, m, by rw [e, iter_half]⟩
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun v' U => WP.block_nil ⟨U.keeps, U.mem, ?_⟩
  rw [U.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem doubleLoop_ok {s : State} {b : Nat} (hb : 0 < b) (hb32 : b < 2 ^ 32) (hd : s.gpr .edx = BitVec.ofNat 32 b) :
    WP isa (.loop (.block [.alu .add .eax (.reg .eax), .alu .sub .edx (.imm 1)]) .ne) s fun t =>
      Keeps [.eax, .edx] s t ∧ t.mem = s.mem ∧ (t.gpr .eax).toNat = (s.gpr .eax).toNat * 2 ^ b % 2 ^ 32 := by
  refine WP.mono (countLoop_ok (fun y => y * 2 % 2 ^ 32) hb hb32 hd fun v => ?_) fun t ⟨K, m, e⟩ =>
    ⟨K, m, by rw [e, ← iter_double, Nat.mod_eq_of_lt (BitVec.isLt _)]⟩
  refine wp_addS rfl fun v' U _ => WP.block_nil ⟨U.keeps, U.mem, ?_⟩
  rw [U.gpr, BitVec.toNat_add, Nat.mul_two]

open VG.Impl.Rsa.X86.RecoverDetRt (lowTest topTest)

/-- `lowTest`: `ecx` the low `b` bits of `eax` (`b` in `sB`). -/
theorem lowTest_ok {s : State} (h : Ws s B Z w N) {b : Nat} (hsB : slot s.mem B sB = b) (hb : 0 < b)
    (hb32 : b < 32) :
    WP isa lowTest s fun t => Keeps [.eax, .ecx, .edx] s t ∧ t.mem = s.mem ∧
      (t.gpr .ecx).toNat = (s.gpr .eax).toNat % 2 ^ b := by
  unfold lowTest
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (wp_movS (v := s.gpr .eax) rfl fun s₁ U₁ _ => wp_movS (readHdr (h.rest U₁.keeps) (by decide))
    fun s₂ U₂ _ => WP.block_nil ?_)
  have d₂ : s₂.gpr .edx = BitVec.ofNat 32 b := by rw [U₂.gpr, U₁.mem, hsB]
  refine WP.seq (WP.mono (halfLoop_ok hb (by omega) d₂) fun s₃ ⟨K₃, m₃, e₃⟩ => ?_)
  have w₃ : Ws s₃ B Z w N := h.rest (rs := [.eax, .ecx, .edx]) ((U₁.keeps.mono (by simp)).trans ((U₂.keeps.mono (by simp)).trans
    (K₃.mono (by simp))))
  refine WP.seq (wp_movS (readHdr w₃ (by decide)) fun s₄ U₄ _ => WP.block_nil ?_)
  have d₄ : s₄.gpr .edx = BitVec.ofNat 32 b := by rw [U₄.gpr, m₃, U₂.mem, U₁.mem, hsB]
  refine WP.seq (WP.mono (doubleLoop_ok hb (by omega) d₄) fun s₅ ⟨K₅, m₅, e₅⟩ => ?_)
  refine VG.X86.Wp.wp_xor fun s₆ U₆ => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact (U₁.keeps.mono (by simp)).trans ((U₂.keeps.mono (by simp)).trans ((K₃.mono (by simp)).trans
      ((U₄.keeps.mono (by simp)).trans ((K₅.mono (by simp)).trans (U₆.keeps.mono (by simp))))))
  · rw [U₆.mem, m₅, U₄.mem, m₃, U₂.mem, U₁.mem]
  · have x := (s.gpr .eax).toNat
    have c₅ : s₅.gpr .ecx = s.gpr .eax := by
      rw [K₅.1 _ (by simp), U₄.other _ (by decide), K₃.1 _ (by simp), U₂.other _ (by decide), U₁.gpr]
    have a₄ : (s₄.gpr .eax).toNat = (s.gpr .eax).toNat / 2 ^ b := by
      rw [U₄.other _ (by decide), e₃, U₂.other _ (by decide), U₁.other _ (by decide)]
    have lt := BitVec.isLt (s.gpr .eax)
    have dm := Nat.div_add_mod (s.gpr .eax).toNat (2 ^ b)
    have a₅ : (s₅.gpr .eax).toNat = 2 ^ b * ((s.gpr .eax).toNat / 2 ^ b) := by
      rw [e₅, a₄, Nat.mod_eq_of_lt (by rw [Nat.mul_comm]; omega), Nat.mul_comm]
    rw [U₆.gpr, BitVec.toNat_xor, c₅, a₅]
    conv => lhs; arg 1; rw [← dm]
    exact xor_high (Nat.mod_lt _ (Nat.two_pow_pos _))

/-- `topTest`: `ecx` the top `b` bits of `eax`, in place (`b` in `sB`). -/
theorem topTest_ok {s : State} (h : Ws s B Z w N) {b : Nat} (hsB : slot s.mem B sB = b) (hb : 0 < b)
    (hb32 : b < 32) :
    WP isa topTest s fun t => Keeps [.eax, .ecx, .edx] s t ∧ t.mem = s.mem ∧
      (t.gpr .ecx).toNat = 2 ^ (32 - b) * ((s.gpr .eax).toNat / 2 ^ (32 - b)) := by
  unfold topTest
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (wp_movS (v := s.gpr .eax) rfl fun s₁ U₁ _ => wp_movS (readHdr (h.rest U₁.keeps) (by decide))
    fun s₂ U₂ _ => WP.block_nil ?_)
  have d₂ : s₂.gpr .edx = BitVec.ofNat 32 b := by rw [U₂.gpr, U₁.mem, hsB]
  refine WP.seq (WP.mono (doubleLoop_ok hb (by omega) d₂) fun s₃ ⟨K₃, m₃, e₃⟩ => ?_)
  have w₃ : Ws s₃ B Z w N := h.rest (rs := [.eax, .ecx, .edx]) ((U₁.keeps.mono (by simp)).trans ((U₂.keeps.mono (by simp)).trans
    (K₃.mono (by simp))))
  refine WP.seq (wp_movS (readHdr w₃ (by decide)) fun s₄ U₄ _ => WP.block_nil ?_)
  have d₄ : s₄.gpr .edx = BitVec.ofNat 32 b := by rw [U₄.gpr, m₃, U₂.mem, U₁.mem, hsB]
  refine WP.seq (WP.mono (halfLoop_ok hb (by omega) d₄) fun s₅ ⟨K₅, m₅, e₅⟩ => ?_)
  refine VG.X86.Wp.wp_xor fun s₆ U₆ => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact (U₁.keeps.mono (by simp)).trans ((U₂.keeps.mono (by simp)).trans ((K₃.mono (by simp)).trans
      ((U₄.keeps.mono (by simp)).trans ((K₅.mono (by simp)).trans (U₆.keeps.mono (by simp))))))
  · rw [U₆.mem, m₅, U₄.mem, m₃, U₂.mem, U₁.mem]
  · have c₅ : s₅.gpr .ecx = s.gpr .eax := by
      rw [K₅.1 _ (by simp), U₄.other _ (by decide), K₃.1 _ (by simp), U₂.other _ (by decide), U₁.gpr]
    have a₄ : (s₄.gpr .eax).toNat = (s.gpr .eax).toNat * 2 ^ b % 2 ^ 32 := by
      rw [U₄.other _ (by decide), e₃, U₂.other _ (by decide), U₁.other _ (by decide)]
    have lt := BitVec.isLt (s.gpr .eax)
    have dm := Nat.div_add_mod (s.gpr .eax).toNat (2 ^ (32 - b))
    have p : (2 : Nat) ^ 32 = 2 ^ (32 - b) * 2 ^ b := by rw [← Nat.pow_add]; congr 1; omega
    have a₅ : (s₅.gpr .eax).toNat = (s.gpr .eax).toNat % 2 ^ (32 - b) := by
      rw [e₅, a₄, p, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    rw [U₆.gpr, BitVec.toNat_xor, c₅, a₅]
    conv => lhs; arg 1; rw [← dm]
    exact xor_low (Nat.mod_lt _ (Nat.two_pow_pos _))

/-! ## The stage flag -/

open VG.Impl.Rsa.X86.RecoverDetRt (flagZero sStg)

/-- `flagZero`: `sStg` one where `ecx` is zero, else zero. -/
theorem flagZero_ok {s : State} {is : List Instr} {Q : State → Prop} (h : Ws s B Z w N)
    (k : ∀ t, Keep B w [] [sStg] s.mem t.mem → slot t.mem B sStg = (if s.gpr .ecx = 0 then 1 else 0) →
      Keeps [.eax] s t → WP isa (.block is) t Q) :
    WP isa (.block (flagZero ++ is)) s Q := by
  unfold flagZero
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (v := 0) rfl fun s₁ U₁ _ => wp_subS (v := s.gpr .ecx) (by rw [readSrc, U₁.other _ (by decide)])
    fun s₂ U₂ c₂ => VG.X86.Wp.wp_sbb_self c₂ fun s₃ U₃ => wp_addS (v := 1) rfl fun s₄ U₄ _ => ?_
  have K₄ : Keeps [.eax] s s₄ := U₁.keeps.trans (U₂.keeps.trans (U₃.keeps.trans U₄.keeps))
  refine storeHdr (h.rest K₄) (by decide) .eax fun t T e k₃ _ _ => k t ?_ ?_ (K₄.trans (k₃.mono (by simp)))
  · rwa [U₄.mem, U₃.mem, U₂.mem, U₁.mem] at T
  · rw [e, U₄.gpr, U₃.gpr, U₁.gpr]
    by_cases z : s.gpr .ecx = 0
    · simp [z]
    · have : 0 < (s.gpr .ecx).toNat := by
        rcases Nat.eq_zero_or_pos (s.gpr .ecx).toNat with e | e
        · exact absurd (BitVec.eq_of_toNat_eq (by rw [e]; rfl)) z
        · exact e
      simp only [z, ite_false, show decide ((0 : BitVec 32).toNat < (s.gpr .ecx).toNat) = true from
        decide_eq_true this, ite_true]
      rfl

/-! ## The stages' operations on the recovery's arrays -/

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
open VG.Proof.Rsa.X86.Keys (arr num upd)
open VG.Impl.Rsa.X86.Recover (nArr)

/-- A word of `K + 1` with its value below `2^(32 K)`: the value is in the low `K` words, the top
one zero. -/
theorem split_top {m : Mem} {d K X : Nat} (h : val32 m B d (K + 1) = X) (hX : X < 2 ^ (32 * K)) :
    val32 m B d K = X ∧ w32 m B (d + 4 * K) = 0 := by
  rw [val32_append] at h
  have lt := val32_lt m B d K
  have p := Nat.two_pow_pos (32 * K)
  have z : val32 m B (d + 4 * K) 1 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * K) 1) with e | e
    · exact e
    · exfalso
      have : 2 ^ (32 * K) ≤ 2 ^ (32 * K) * val32 m B (d + 4 * K) 1 := Nat.le_mul_of_pos_right _ e
      omega
  refine ⟨by rw [z, Nat.mul_zero, Nat.add_zero] at h; exact h, ?_⟩
  have := z
  simp only [val32, Nat.mul_zero, Nat.add_zero] at this
  exact this

theorem KS.sC4_slot (h : KS g s0 A live AW liveW V ls s) {c : Nat} (hC : VG.Impl.Rsa.X86.RecoverDetRt.sC4 ∈ ls)
    (hV : V VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c) :
    slot s.mem g.B VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c := by
  rw [h.sl _ hC, hV]

/-- `[o] := [a] / 2^(32 c)` (narrow, `4 c` in `sC4`), the word above `[o]` zero. -/
theorem KS.moveDown_w {o a c : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hoa : o ≠ a) (hc : c < g.w)
    (hC : VG.Impl.Rsa.X86.RecoverDetRt.sC4 ∈ ls) (hV : V VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.moveH VG.Impl.Rsa.X86.RecoverRt.nar a o true false) s fun t =>
      KS g s0 (upd A o (A a / 2 ^ (32 * c))) (o :: live) AW liveW V ls t ∧ Keeps opRegs s t ∧
      w32 t.mem g.B (arr g.w o + 4 * g.w) = 0 := by
  have kc : c < VG.Proof.Rsa.X86.KeyRt.kw (8 * g.n + 8) := by rw [kw_nar]; exact hc
  refine WP.mono (moveDown_ok h.rt (h.live_lt a ha) ho (Ne.symm hoa) kc (h.sC4_slot hC hV))
    fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_nar] at k e
  have lt : num s.mem g.B g.w a / 2 ^ (32 * c) < 2 ^ (32 * g.w) :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (val32_lt _ _ _ _)
  obtain ⟨e₁, e₂⟩ := split_top e lt
  refine ⟨h.write_w k ho (by simp) (r.mono (by decide)) ?_ hlW (by simp), r.mono (by decide), e₂⟩
  rw [num, e₁, h.arrs a ha]

/-- `[o] := [a] / 2^(32 c)` (wide, `4 c` in `sC4`), the word above `[o]` zero. -/
theorem KS.moveDown_W {o a c : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < 22) (ha : a ∈ liveW) (hoa : o ≠ a) (hc : c < g.W)
    (hC : VG.Impl.Rsa.X86.RecoverDetRt.sC4 ∈ ls) (hV : V VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c)
    (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.moveH VG.Impl.Rsa.X86.RecoverRt.wid a o true false) s fun t =>
      KS g s0 A live (upd AW o (AW a / 2 ^ (32 * c))) (o :: liveW) V ls t ∧ Keeps opRegs s t ∧
      w32 t.mem g.B (arr g.W o + 4 * g.W) = 0 := by
  have kc : c < VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) := by rw [kw_wid]; exact hc
  refine WP.mono (moveDown_ok h.rtW (h.liveW_lt a ha) ho (Ne.symm hoa) kc (h.sC4_slot hC hV))
    fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_wid] at k e
  have lt : num s.mem g.B g.W a / 2 ^ (32 * c) < 2 ^ (32 * g.W) :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (val32_lt _ _ _ _)
  obtain ⟨e₁, e₂⟩ := split_top e lt
  refine ⟨h.write_W k ho (by simp) (r.mono (by decide)) ?_ hl (by simp), r.mono (by decide), e₂⟩
  rw [num, e₁, h.arrsW a ha]

/-- `[o] := [a] 2^(32 c) mod 2^(32 W)` (wide, `4 c` in `sC4`), the word above `[o]` zero. -/
theorem KS.moveUp_W {o a c : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < 22) (ha : a ∈ liveW) (hoa : o ≠ a) (hc : c < g.W)
    (hC : VG.Impl.Rsa.X86.RecoverDetRt.sC4 ∈ ls) (hV : V VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c)
    (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.moveH VG.Impl.Rsa.X86.RecoverRt.wid a o false true) s fun t =>
      KS g s0 A live (upd AW o (AW a * 2 ^ (32 * c) % 2 ^ (32 * g.W))) (o :: liveW) V ls t ∧
      Keeps opRegs s t ∧ w32 t.mem g.B (arr g.W o + 4 * g.W) = 0 := by
  have kc : c < VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) := by rw [kw_wid]; exact hc
  refine WP.mono (moveUp_ok h.rtW (h.liveW_lt a ha) ho (Ne.symm hoa) kc (h.sC4_slot hC hV))
    fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_wid] at k e
  obtain ⟨e₁, e₂⟩ := split_top e (Nat.mod_lt _ (Nat.two_pow_pos _))
  refine ⟨h.write_W k ho (by simp) (r.mono (by decide)) ?_ hl (by simp), r.mono (by decide), e₂⟩
  rw [num, e₁, h.arrsW a ha]

/-- `flagZero` on the recovery's arrays: `sStg` one where `ecx` is zero. -/
theorem KS.flagZero (h : KS g s0 A live AW liveW V ls s) :
    WP isa (.block VG.Impl.Rsa.X86.RecoverDetRt.flagZero) s fun t =>
      KS g s0 A live AW liveW (upd V sStg (if s.gpr .ecx = 0 then 1 else 0)) (sStg :: ls) t ∧
      Keeps [.eax] s t := by
  rw [← List.append_nil VG.Impl.Rsa.X86.RecoverDetRt.flagZero]
  refine flagZero_ok h.ws fun t k e r => WP.block_nil ⟨h.slot1 k (by decide) (r.mono (by decide)) e, r⟩

/-- `orLowH` on the recovery's arrays: `ecx` zero exactly where the low `c` words of `[a]` and
`[b]` are (`4 c` in `sC4`). -/
theorem KS.orLowH {a b c : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ha : a ∈ live) (hb : b ∈ live) (hc0 : 0 < c) (hc : c ≤ g.w)
    (hC : VG.Impl.Rsa.X86.RecoverDetRt.sC4 ∈ ls) (hV : V VG.Impl.Rsa.X86.RecoverDetRt.sC4 = 4 * c) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.orLowH a b) s fun t =>
      KS g s0 A live AW liveW V ls t ∧ Keeps opRegs s t ∧
      (t.gpr .ecx = 0 ↔ (A a % 2 ^ (32 * c) = 0 ∧ A b % 2 ^ (32 * c) = 0)) := by
  have kc : c ≤ VG.Proof.Rsa.X86.KeyRt.kw (8 * g.n + 8) := by rw [kw_nar]; exact hc
  refine WP.mono (orLowH_ok h.rt (h.live_lt a ha) (h.live_lt b hb) hc0 kc (h.sC4_slot hC hV))
    fun t ⟨m, r, e⟩ => ?_
  rw [kw_nar, h.arrs a ha, h.arrs b hb] at e
  have r' : Keeps opRegs s t := r.mono (by decide)
  exact ⟨h.of_rest r' (fun x hx => hx) m, r', e⟩

end

end VG.Proof.Rsa.X86.Recover
