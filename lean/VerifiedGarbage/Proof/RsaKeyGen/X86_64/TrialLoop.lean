import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial

/-!
# A candidate on x86-64: the trial division's table and loop

`extBase j` is the base of array `j ≥ 7` (`extBase_ok`); `tabWrite` writes
the table (`tabWrite_ok`); `trial` runs `trialEntry` for the four entries of
each of its first `N` words, and leaves ZF clear iff one divides `c`
(`trial_ok`): `trialAny N c`.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem slot_ext (w j : Nat) (hj : 7 ≤ j) : slot w j = slot w aOne + (j - 7) * (8 * (w + 2)) := by
  unfold slot aOne; rw [Nat.add_assoc, ← Nat.add_mul, show 7 + (j - 7) = j by omega]

/-- `n` additions of `rax = V` to `r`. -/
theorem addRep_ok {B : Addr} {r : Reg} (hr : r ≠ .rax)
    (hwo : writesOnly [r] (.block [.alu .add r (.reg .rax)]) = true) {V : Nat} :
    ∀ (n a : Nat) (t : State), t.gpr .rax = BitVec.ofNat 64 V → t.gpr r = off B a →
      WP isa (.block (List.replicate n (.alu .add r (.reg .rax)))) t fun t' =>
        t'.gpr r = off B (a + n * V) ∧ t'.mem = t.mem ∧ Keep [r] t t'
  | 0, a, t, _, h => WP.block_nil ⟨by rw [Nat.zero_mul, Nat.add_zero]; exact h, rfl, Keep.refl _ _⟩
  | n + 1, a, t, hax, h => by
    rw [List.replicate_succ, show ∀ (x : Instr) l, x :: l = [x] ++ l from fun _ _ => rfl, WP.block_append_iff]
    refine WP.mono (WP.keep [r] (Q := fun t₁ => t₁.gpr r = off B (a + V) ∧ t₁.mem = t.mem) (by
      xrun [h, hax, off_off]) hwo) fun t₁ ⟨⟨h₁, hm₁⟩, k₁⟩ => ?_
    refine WP.mono (addRep_ok hr hwo (V := V) n (a + V) t₁ (by rw [k₁.gpr (by simp [hr.symm])]; exact hax) h₁)
      fun t' ⟨h', hm', k'⟩ => ⟨by rw [h', Nat.add_assoc, Nat.add_mul, Nat.one_mul, Nat.add_comm V], hm'.trans hm₁,
        (k₁.trans k').mono (by simp)⟩

/-- `8 (w + 2)`, the bytes of an array, into `rax`. -/
theorem arrBytes_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : w < 2 ^ 31) :
    WP isa (.block [.mov .rax (.mem (hdr sW)), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax)]) s fun t => t.gpr .rax = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 := hg.scr.ld (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.hw, sx2]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (2 : BitVec 64).toNat = 2 := rfl
    rw [this]; have := hw; omega) rfl) fun t ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩

/-- `extBase j r`: the base of array `j ≥ 7` into `r`. -/
theorem extBase_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : w < 2 ^ 31) {j : Nat} (hj : 7 ≤ j) {r : Reg}
    (hr : r ≠ .rax) (hw1 : writesOnly [r] (.block [.mov r (.mem (hdr (sArr aOne)))]) = true)
    (hw2 : writesOnly [r] (.block [.alu .add r (.reg .rax)]) = true) :
    WP isa (.block (extBase j r)) s fun t => t.gpr r = off B (slot w j) ∧ t.mem = s.mem ∧ Keep [.rax, r] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr aOne)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show sArr aOne < 32 by decide); omega)
  unfold extBase
  rw [show ∀ l : List Instr, [.mov .rax (.mem (hdr sW)), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .mov r (.mem (hdr (sArr aOne)))] ++ l =
      [.mov .rax (.mem (hdr sW)), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax)] ++ ([.mov r (.mem (hdr (sArr aOne)))] ++ l) from fun _ => rfl,
    WP.block_append_iff]
  refine WP.mono (arrBytes_ok hg hZ hw) fun t₁ ⟨hax₁, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [r] (Q := fun t₂ => t₂.gpr r = off B (slot w aOne) ∧ t₂.mem = t₁.mem) (by
    xrun [State.ea, hdr, (k₁.gpr (by decide)).trans hg.rdi, hdrOff, show InRegions (t₁.rd ++ t₁.wr) _ 8 by
      rw [k₁.2.1, k₁.2.2]; exact hl, hm₁, hg.hdr.harr aOne (by decide)]) hw1) fun t₂ ⟨⟨h₂, hm₂⟩, k₂⟩ => ?_
  refine WP.mono (addRep_ok hr hw2 (V := 8 * (w + 2)) (j - 7) _ t₂ (by rw [k₂.gpr (by simp [hr.symm])]; exact hax₁) h₂)
    fun t ⟨h, hm, k⟩ => ⟨by rw [h, ← slot_ext w j hj], hm.trans (hm₂.trans hm₁), ((k₁.trans k₂).trans k).mono (by simp)⟩

/-- The first `n` words of the table at `T` (in `rbx`). -/
theorem tabWrites_ok {s : State} {B : Addr} {Z T : Nat} (hs : Scr s B Z) (hT : T + 2048 ≤ Z)
    (hbx : s.gpr .rbx = off B T) : ∀ n ≤ 256,
    WP isa (.block ((List.range n).flatMap tabStore)) s fun t =>
      (∀ i < n, word t.mem B (T + 8 * i) = BitVec.ofNat 64 (tabWord i)) ∧ Outside B T (8 * n) s.mem t.mem ∧
      Keep [.rax] s t
  | 0, _ => WP.block_nil ⟨fun i hi => absurd hi (by omega), Outside.refl _ _ _ _, Keep.refl _ _⟩
  | n + 1, hn => by
    have hb := hs.nowrap
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (tabWrites_ok hs hT hbx n (by omega)) fun t ⟨hv, ho, k⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hst : InRegions t.wr (off B (T + 8 * n)) 8 := by rw [k.2.2]; exact hs.st (by omega)
    have hea : t.gpr .rbx + BitVec.ofInt 64 (8 * (n : Int)) = off B (T + 8 * n) := by
      rw [k.gpr (by decide), hbx, hdrOff, off_off]
    refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem.writeW (off B (T + 8 * n))
      (BitVec.ofNat 64 (tabWord n))) (by
      unfold tabStore
      xrun [State.ea, hea, hst]) rfl) fun t' ⟨hm, k'⟩ => ⟨fun i hi => ?_, ?_, (k.trans k').mono (by decide)⟩
    · rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [(writeW_outside t.mem B _ (by omega)).word (by omega) (by omega)]; exact hv i hi
      · exact word_writeW_self _ _ _ _
    · rw [hm]
      intro x hx
      rw [writeW_outside t.mem B _ (by omega) x (by omega)]
      exact ho x (by omega)

theorem mask_or2 (a b : Bool) : mask a ||| mask b = mask (a || b) := by cases a <;> cases b <;> decide

/-- Trial division by the first `m` entries of the table. -/
def anyPre (c m : Nat) : Bool := (List.range m).any fun i => c % tabEntry i == 0

theorem anyPre_succ (c m : Nat) : anyPre c (m + 1) = (anyPre c m || c % tabEntry m == 0) := by
  unfold anyPre; rw [List.range_succ, List.any_append]; simp

/-- What `trial`'s loop keeps, after `k` words of the table at `T`. -/
structure TLInv (s₀ : State) (B : Addr) (Z w T N : Nat) (minv : BitVec 64) (k : Nat) (t : State) : Prop where
  good : Good t B Z w minv
  r13 : t.gpr .r13 = BitVec.ofNat 64 k
  n : word t.mem B (8 * kT0) = BitVec.ofNat 64 N
  tab : ∀ i < 256, word t.mem B (T + 8 * i) = BitVec.ofNat 64 (tabWord i)
  c : wv t.mem B (slot w aN) w = wv s₀.mem B (slot w aN) w
  frm : Frm B [(8 * kT1, 8), (8 * kT2, 8)] s₀.mem t.mem
  keep : Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s₀ t

/-- One table entry, from the loop's invariant. -/
theorem tlEntry_ok {s₀ : State} {B : Addr} {Z w T N : Nat} {minv : BitVec 64} (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hT : 8 * kT2 + 8 ≤ T) (hTZ : T + 2048 ≤ Z) {k j : Nat} (hk : k < 256) (hj : j < 4) {t : State}
    (hI : TLInv s₀ B Z w T N minv k t) (hf : word t.mem B (8 * kT2) = mask (anyPre (wv s₀.mem B (slot w aN) w) (4 * k + j)))
    (hT1 : word t.mem B (8 * kT1) = BitVec.ofNat 64 (tabWord k)) :
    WP isa (seqs (trialEntry j)) t fun t' => TLInv s₀ B Z w T N minv k t' ∧
      word t'.mem B (8 * kT2) = mask (anyPre (wv s₀.mem B (slot w aN) w) (4 * k + j + 1)) ∧
      word t'.mem B (8 * kT1) = BitVec.ofNat 64 (tabWord k) := by
  have hn := hI.good.scr.nowrap
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have h2 : 8 * kT2 + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  refine WP.mono (trialEntry_ok hI.good hZ hw hw' hk hj hT1) fun t' ⟨hf', hg', ho', k'⟩ => ⟨⟨hg', ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [k'.gpr (by decide)]; exact hI.r13
  · rw [ho'.word (Or.inl (by unfold kT0 kT2 sFn; omega)) (by unfold kT0 sFn; omega)]; exact hI.n
  · intro i hi; rw [ho'.word (Or.inr (by omega)) (by omega)]; exact hI.tab i hi
  · rw [ho'.wv (Or.inr h2) (by omega)]; exact hI.c
  · exact hI.frm.trans (Frm.of_outside ho' (by simp))
  · exact (hI.keep.trans k').mono (by decide)
  · rw [hf', hf, hI.c, mask_or2, anyPre_succ, Bool.or_comm]
    congr 2
  · rw [ho'.word (Or.inl (by unfold kT1 kT2 sFn; omega)) (by unfold kT1 sFn; omega)]; exact hT1

/-- Word `k` of the table into `kT1`. -/
theorem tlLoad_ok {s₀ : State} {B : Addr} {Z w N : Nat} {minv : BitVec 64} (hZ : slot w 8 ≤ Z)
    (hw' : w < 2 ^ 31) (hTZ : slot w aTab + 2048 ≤ Z) {k : Nat} (hk : k < 256) {t : State}
    (hI : TLInv s₀ B Z w (slot w aTab) N minv k t) :
    WP isa (.block (extBase aTab .rbx ++ ([.mov .rax (.mem (ix .rbx .r13)), .store (hdr kT1) .rax] : List Instr))) t fun t' =>
      TLInv s₀ B Z w (slot w aTab) N minv k t' ∧ word t'.mem B (8 * kT1) = BitVec.ofNat 64 (tabWord k) ∧
      word t'.mem B (8 * kT2) = word t.mem B (8 * kT2) := by
  have hn := hI.good.scr.nowrap
  have hT2 : 8 * kT2 + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have hTa : slot w aN ≤ slot w aTab := by unfold slot aN aTab; omega
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  rw [WP.block_append_iff]
  refine WP.mono (extBase_ok hI.good hZ hw' (j := aTab) (by decide) (r := .rbx) (by decide) rfl rfl)
    fun t₁ ⟨hbx, hm₁, k₁⟩ => ?_
  have hs₁ := hI.good.scr.congr k₁.2.2
  have hst : InRegions t₁.wr (off B (8 * kT1)) 8 := hs₁.st (by have := hdr_lt_slot w 8 (show kT1 < 32 by decide); omega)
  have hld : InRegions (t₁.rd ++ t₁.wr) (off B (slot w aTab + 8 * k)) 8 := hs₁.ld (by omega)
  have h13 : t₁.gpr .r13 = BitVec.ofNat 64 k := (k₁.gpr (by decide)).trans hI.r13
  have hdi : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hI.good.rdi
  have hv : word t₁.mem B (slot w aTab + 8 * k) = BitVec.ofNat 64 (tabWord k) := by rw [hm₁]; exact hI.tab k hk
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₁.mem.writeW (off B (8 * kT1)) (BitVec.ofNat 64 (tabWord k)))
    (by xrun [State.ea, ix, addr0 hbx h13, hld, hv, hdr, hdi, hdrOff, hst]) rfl) fun t' ⟨hm, k'⟩ => ?_
  have ho : Outside B (8 * kT1) 8 t.mem t'.mem := by
    rw [hm, hm₁]; exact writeW_outside _ _ _ (by have := hdr_lt_slot w 8 (show kT1 < 32 by decide); omega)
  refine ⟨⟨⟨hs₁.congr k'.2.2, (k'.gpr (by decide)).trans hdi, by rw [hm, hm₁]; exact hI.good.hdr.store (by decide) (by decide) _⟩,
    (k'.gpr (by decide)).trans h13, ?_, fun i hi => ?_, ?_, hI.frm.trans (Frm.of_outside ho (by simp)),
    ((hI.keep.trans k₁).trans k').mono (by decide)⟩, by rw [hm]; exact word_writeW_self _ _ _ _, ?_⟩
  · rw [ho.word (Or.inl (by unfold kT0 kT1 sFn; omega)) (by unfold kT0 sFn; omega)]; exact hI.n
  · rw [ho.word (Or.inr (by have := hdr_lt_slot w aN (show kT1 < 32 by decide); omega)) (by omega)]; exact hI.tab i hi
  · rw [ho.wv (Or.inr (by have := hdr_lt_slot w aN (show kT1 < 32 by decide); omega)) (by omega)]; exact hI.c
  · rw [ho.word (Or.inr (by unfold kT1 kT2 sFn; omega)) (by unfold kT2 sFn; omega)]

/-- One word of the table: its four entries, and the count. -/
theorem tlIter_ok {s₀ : State} {B : Addr} {Z w N : Nat} {minv : BitVec 64} (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hTZ : slot w aTab + 2048 ≤ Z) (hN : N ≤ 256) {k : Nat} (hk : k < N) {t : State}
    (hI : TLInv s₀ B Z w (slot w aTab) N minv k t)
    (hf : word t.mem B (8 * kT2) = mask (anyPre (wv s₀.mem B (slot w aN) w) (4 * k))) :
    WP isa (seqs (([.block (extBase aTab .rbx ++ ([.mov .rax (.mem (ix .rbx .r13)), .store (hdr kT1) .rax] : List Instr))] : List (Prog isa)) ++
      trialEntry 0 ++ trialEntry 1 ++ trialEntry 2 ++ trialEntry 3 ++
      ([.block [.alu .add .r13 (.imm 1), .mov .rax (.mem (hdr kT0)), .alu .cmp .r13 (.reg .rax)]] : List (Prog isa)))) t fun t' =>
      t'.zf = some (decide (k + 1 = N)) ∧ TLInv s₀ B Z w (slot w aTab) N minv (k + 1) t' ∧
      word t'.mem B (8 * kT2) = mask (anyPre (wv s₀.mem B (slot w aN) w) (4 * (k + 1))) := by
  have hT : 8 * kT2 + 8 ≤ slot w aTab := hdr_lt_slot w aTab (by decide)
  simp only [List.append_assoc, List.cons_append]
  refine WP.seq (WP.mono (tlLoad_ok hZ hw' hTZ (by omega) hI) fun t₁ ⟨hI₁, hT1₁, hf₁⟩ => ?_)
  rw [hf] at hf₁
  have e := fun j (hj : j < 4) t (hI : TLInv s₀ B Z w (slot w aTab) N minv k t) hf hT1 =>
    tlEntry_ok (j := j) hZ hw hw' hT hTZ (by omega) hj hI hf hT1
  refine wp_seqs_append (a := trialEntry 0) (by simp [trialEntry]) (by simp) (WP.mono (e 0 (by decide) t₁ hI₁ (by rw [hf₁, Nat.add_zero]) hT1₁)
    fun t₂ ⟨hI₂, hf₂, hT1₂⟩ => ?_)
  refine wp_seqs_append (a := trialEntry 1) (by simp [trialEntry]) (by simp) (WP.mono (e 1 (by decide) t₂ hI₂ (by rw [hf₂, Nat.add_zero]) hT1₂)
    fun t₃ ⟨hI₃, hf₃, hT1₃⟩ => ?_)
  refine wp_seqs_append (a := trialEntry 2) (by simp [trialEntry]) (by simp) (WP.mono (e 2 (by decide) t₃ hI₃ (by rw [hf₃]) hT1₃)
    fun t₄ ⟨hI₄, hf₄, hT1₄⟩ => ?_)
  refine wp_seqs_append (a := trialEntry 3) (by simp [trialEntry]) (by simp) (WP.mono (e 3 (by decide) t₄ hI₄ (by rw [hf₄]) hT1₄)
    fun t₅ ⟨hI₅, hf₅, _⟩ => ?_)
  have hn := hI₅.good.scr.nowrap
  have hl : InRegions (t₅.rd ++ t₅.wr) (off B (8 * kT0)) 8 :=
    hI₅.good.scr.ld (by have := hdr_lt_slot w 8 (show kT0 < 32 by decide); omega)
  simp only [seqs]
  refine WP.mono (WP.keep [.r13, .rax] (Q := fun t' => t'.zf = some (decide (k + 1 = N)) ∧
      t'.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧ t'.mem = t₅.mem) (by
    xrun [State.ea, hdr, hI₅.good.rdi, hdrOff, hl, hI₅.n, hI₅.r13, ofNat_add_one,
      ofNat_sub_beq (show k + 1 < 2 ^ 64 by omega) (show N < 2 ^ 64 by omega)]) rfl) fun t' ⟨⟨hz, h13, hm⟩, k'⟩ =>
    ⟨hz, ⟨⟨hI₅.good.scr.congr k'.2.2, (k'.gpr (by decide)).trans hI₅.good.rdi, by rw [hm]; exact hI₅.good.hdr⟩,
      h13, by rw [hm]; exact hI₅.n, fun i hi => by rw [hm]; exact hI₅.tab i hi, by rw [hm]; exact hI₅.c,
      by rw [hm]; exact hI₅.frm, (hI₅.keep.trans k').mono (by decide)⟩, by rw [hm, hf₅, show 4 * k + 3 + 1 = 4 * (k + 1) by omega]⟩

/-- `trial`: ZF clear iff one of the first `4 N` entries of the table divides
`c`, `N = 256` for `w > 16` and 128 otherwise. -/
theorem trial_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw : 1 ≤ w) (hw64 : w ≤ 64) :
    WP isa (seqs trial) s fun t =>
      t.zf = some (!trialAny (if 17 ≤ w then 256 else 128) (wv s.mem B (slot w aN) w)) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  have hn := hg.scr.nowrap
  have hT2 : 8 * kT2 + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have hTa : slot w aN + 8 * (w + 2) ≤ slot w aTab := by unfold slot aN aTab; omega
  have hTa' : 8 * kT2 + 8 ≤ slot w aTab := hdr_lt_slot w aTab (by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  unfold trial
  simp only [seqs]
  -- The table, and the number of its words to use.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (extBase_ok hg hZ (by omega) (j := aTab) (by decide) (r := .rbx) (by decide) rfl rfl)
    fun s₁ ⟨hbx₁, hm₁, k₁⟩ => ?_
  refine WP.mono (tabWrites_ok (hg.scr.congr k₁.2.2) hTZ hbx₁ 256 (Nat.le_refl _)) fun s₂ ⟨htab₂, ho₂, k₂⟩ => ?_
  have hm₂ : ∀ i < 32, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [ho₂.word (Or.inl (by have := hdr_lt_slot w aTab hi; omega)) (by omega), hm₁]
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2]; exact hl i hi
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 128 ∧ t.cf = some (decide (w < 17)) ∧
      t.mem = s₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ sW (by decide), hm₂ sW (by decide), hg.hdr.hw, sx_ofNat]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (BitVec.signExtend 64 (17 : BitVec 32)).toNat = 17 by decide]) rfl) fun s₃ ⟨⟨hax₃, hcf₃, hm₃⟩, k₃⟩ => ?_
  have hg₃ : Good s₃ B Z w minv := ⟨hg.scr.congr (k₃.2.2.trans (k₂.2.2.trans k₁.2.2)), (k₃.gpr (by decide)).trans hdi₂,
    ⟨by rw [hm₃, hm₂ sW (by decide)]; exact hg.hdr.hw, by rw [hm₃, hm₂ sMinv (by decide)]; exact hg.hdr.hminv,
      fun j hj => by rw [hm₃, hm₂ (sArr j) (by unfold sArr; omega)]; exact hg.hdr.harr j hj⟩⟩
  have hc₃ : wv s₃.mem B (slot w aN) w = wv s.mem B (slot w aN) w := by
    rw [hm₃, ho₂.wv (k := w) (Or.inl (by omega)) (by omega), hm₁]
  have ho₃ : Outside B (slot w aTab) 2048 s.mem s₃.mem := by rw [hm₃, ← hm₁]; exact ho₂
  generalize hNdef : (if 17 ≤ w then 256 else 128) = N
  have hN : N ≤ 256 ∧ 1 ≤ N := by rw [← hNdef]; split <;> omega
  have hN128 : w < 17 → N = 128 := fun h => by rw [← hNdef]; split <;> omega
  have hN256 : ¬ w < 17 → N = 256 := fun h => by rw [← hNdef]; split <;> omega
  -- From `rax = N`: the counts, the loop and ZF.
  have cont : ∀ t : State, t.gpr .rax = BitVec.ofNat 64 N → t.mem = s₃.mem → Keep [.rax] s₃ t →
      WP isa (.seq (.block [.store (hdr kT0) .rax, .mov32 .rax (.imm 0), .store (hdr kT2) .rax, .mov32 .r13 (.imm 0)])
        (.seq (.loop (seqs ([.block (extBase aTab .rbx ++ [.mov .rax (.mem (ix .rbx .r13)), .store (hdr kT1) .rax])] ++
          trialEntry 0 ++ trialEntry 1 ++ trialEntry 2 ++ trialEntry 3 ++
          [.block [.alu .add .r13 (.imm 1), .mov .rax (.mem (hdr kT0)), .alu .cmp .r13 (.reg .rax)]])) .ne)
          (.block [.mov .rax (.mem (hdr kT2)), .alu .test .rax (.reg .rax)]))) t fun t =>
      t.zf = some (!trialAny N (wv s.mem B (slot w aN) w)) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
    intro t hax hmt kt
    have hgt : Good t B Z w minv := ⟨hg₃.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg₃.rdi, by rw [hmt]; exact hg₃.hdr⟩
    have hst : ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun i hi => hgt.scr.st (by have := hdr_lt_slot w 8 hi; omega)
    refine WP.seq (WP.mono (WP.keep [.rax, .r13] (Q := fun t' => t'.mem = (t.mem.writeW (off B (8 * kT0))
        (BitVec.ofNat 64 N)).writeW (off B (8 * kT2)) (0 : BitVec 64) ∧ t'.gpr .r13 = BitVec.ofNat 64 0) (by
      xrun [State.ea, hdr, hgt.rdi, hdrOff, hst kT0 (by decide), hst kT2 (by decide), hax, sx_ofNat]
      rfl) rfl) fun t₄ ⟨⟨hm₄, h13₄⟩, k₄⟩ => ?_)
    have hoA : Outside B (8 * kT0) 8 t.mem (t.mem.writeW (off B (8 * kT0)) (BitVec.ofNat 64 N)) :=
      writeW_outside _ _ _ (by unfold kT0 sFn; omega)
    have hoB : ∀ m : Mem, Outside B (8 * kT2) 8 m (m.writeW (off B (8 * kT2)) (0 : BitVec 64)) :=
      fun m => writeW_outside _ _ _ (by unfold kT2 sFn; omega)
    have hg₄ : Good t₄ B Z w minv := ⟨hgt.scr.congr k₄.2.2, (k₄.gpr (by decide)).trans hgt.rdi,
      by rw [hm₄]; exact (hgt.hdr.store (by decide) (by decide) _).store (by decide) (by decide) _⟩
    have hc₄ : wv t₄.mem B (slot w aN) w = wv s.mem B (slot w aN) w := by
      rw [hm₄, (hoB _).wv (Or.inr hT2) (by omega), hoA.wv (Or.inr (by unfold kT0 kT2 sFn at *; omega)) (by omega), hmt, hc₃]
    have hN₄ : word t₄.mem B (8 * kT0) = BitVec.ofNat 64 N := by
      rw [hm₄, (hoB _).word (Or.inl (by unfold kT0 kT2 sFn; omega)) (by unfold kT0 sFn; omega), word_writeW_self]
    have htab₄ : ∀ i < 256, word t₄.mem B (slot w aTab + 8 * i) = BitVec.ofNat 64 (tabWord i) := fun i hi => by
      rw [hm₄, (hoB _).word (Or.inr (by omega)) (by omega),
        hoA.word (Or.inr (by have := hdr_lt_slot w aTab (show kT0 < 32 by decide); omega)) (by omega),
        hmt, hm₃]; exact htab₂ i hi
    have hf₄ : word t₄.mem B (8 * kT2) = mask (anyPre (wv t₄.mem B (slot w aN) w) (4 * 0)) := by
      rw [hm₄, word_writeW_self]; unfold anyPre; rw [Nat.mul_zero, show List.range 0 = [] from rfl, List.any_nil, mask_false]
    refine WP.seq (WP.mono (wp_upto (a := 0) (N := N) (by omega)
      (fun k t' => TLInv t₄ B Z w (slot w aTab) N minv k t' ∧
        word t'.mem B (8 * kT2) = mask (anyPre (wv t₄.mem B (slot w aN) w) (4 * k)))
      (fun k _ hk t' ⟨hI, hf⟩ => WP.mono (tlIter_ok hZ hw (by omega) hTZ hN.1 hk hI hf)
        fun t'' ⟨hz, hI', hf'⟩ => ⟨hz, hI', hf'⟩) (fun t' h => h)
      ⟨⟨hg₄, h13₄, hN₄, htab₄, rfl, Frm.refl _ _ _, Keep.refl _ _⟩, hf₄⟩) fun t₅ ⟨hI₅, hf₅⟩ => ?_)
    have hl₅ : InRegions (t₅.rd ++ t₅.wr) (off B (8 * kT2)) 8 :=
      hI₅.good.scr.ld (by have := hdr_lt_slot w 8 (show kT2 < 32 by decide); omega)
    refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (!trialAny N (wv s.mem B (slot w aN) w)) ∧
        t'.mem = t₅.mem) (by
      xrun [State.ea, hdr, hI₅.good.rdi, hdrOff, hl₅, hf₅, BitVec.and_self, hc₄]
      unfold trialAny anyPre
      cases ((List.range (4 * N)).any fun i => wv s.mem B (slot w aN) w % tabEntry i == 0) <;> decide) rfl)
      fun t' ⟨⟨hz, hm'⟩, k'⟩ => ⟨hz, ⟨hI₅.good.scr.congr k'.2.2, (k'.gpr (by decide)).trans hI₅.good.rdi,
        by rw [hm']; exact hI₅.good.hdr⟩, ?_, ?_⟩
    · intro x hx
      rw [hm', hI₅.frm x (fun r hr => hx r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])), hm₄,
        hoB _ x (hx (8 * kT2, 8) (by simp)), hoA x (hx (8 * kT0, 8) (by simp)), hmt,
        ho₃ x (hx (slot w aTab, 2048) (by simp))]
    · exact (((((k₁.trans k₂).trans k₃).trans kt).trans k₄).trans hI₅.keep |>.trans k').mono (by decide)
  refine WP.seq (WP.ite (decide (w < 17)) (by simp [eval, hcf₃]) (fun h => WP.block_nil (cont s₃ ?_ rfl (Keep.refl _ _)))
    (fun h => WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 N ∧ t.mem = s₃.mem) (by
      xrun [sx_ofNat]; rw [hN256 (by simpa using h)]; rfl) rfl) fun t ⟨⟨h1, h2⟩, k⟩ => cont t h1 h2 k))
  rw [hax₃, hN128 (by simpa using h)]

end VG.Proof.RsaKeyGen.X86_64
