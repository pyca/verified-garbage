import VerifiedGarbage.Proof.Bignum.AArch64.PcCode

/-!
# RSA on AArch64: `R² mod m` is constant time but for `m`

`double` and `doubles` (`doubles_ct`), whose count is public, the squarings
(`sqs_ct`) and the computation of `R² mod m` (`r2_ct`), which branches on
the top word of the public modulus.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)

/-! ## Sequences -/

theorem exec_seqs_append {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s s' : State} {t}
    (e : Exec isa (seqs (a ++ b)) s t s') : Exec isa (.seq (seqs a) (seqs b)) s t s' := by
  induction a generalizing s t with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact e
    | cons d rest =>
      change Exec isa (.seq c (seqs (d :: rest ++ b))) s t s' at e
      change Exec isa (.seq (.seq c (seqs (d :: rest))) (seqs b)) s t s'
      obtain ⟨t₁, t₂, s₁, rfl, e₁, e₂⟩ : ∃ t₁ t₂ s₁, t = t₁ ++ t₂ ∧ Exec isa c s t₁ s₁ ∧
          Exec isa (seqs (d :: rest ++ b)) s₁ t₂ s' := by
        cases e with
        | seq e₁ e₂ => exact ⟨_, _, _, rfl, e₁, e₂⟩
      have e₂' := ih (by simp) e₂
      obtain ⟨u₁, u₂, s₂, rfl, f₁, f₂⟩ : ∃ u₁ u₂ s₂, t₂ = u₁ ++ u₂ ∧ Exec isa (seqs (d :: rest)) s₁ u₁ s₂ ∧
          Exec isa (seqs b) s₂ u₂ s' := by
        cases e₂' with
        | seq f₁ f₂ => exact ⟨_, _, _, rfl, f₁, f₂⟩
      rw [← List.append_assoc]
      exact .seq (.seq e₁ f₁) f₂

theorem RelCT.seqs_append {P Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h : RelCT isa P (.seq (seqs a) (seqs b)) Q) : RelCT isa P (seqs (a ++ b)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_seqs_append ha hb e₁) (exec_seqs_append ha hb e₂)

/-- Two runs related with the same `a` are related with the same `b`. -/
theorem two_bind {α β : Type} {Φ : α → State → Prop} {Ψ : β → State → Prop}
    (f : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → ∃ b, Ψ b s₁ ∧ Ψ b s₂) {s₁ s₂ : State} (h : Two Φ s₁ s₂) :
    Two Ψ s₁ s₂ :=
  let ⟨a, h₁, h₂, hsp⟩ := h
  let ⟨b, g₁, g₂⟩ := f a s₁ s₂ h₁ h₂
  ⟨b, g₁, g₂, hsp⟩

/-- `Good` after code that changes no memory and not `x0`. -/
theorem Good.keep {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hm : t.mem = s.mem) {rs : List Reg} (k : Keep rs s t) (h0 : .x0 ∉ rs) : Good t B Z w minv :=
  ⟨hg.scr.congr k.wr, (k.gpr .x0 h0).trans hg.x0, hm ▸ hg.hdr⟩

theorem GoodL.keep {L : Lay} {s t : State} (hg : GoodL L s) (hm : t.mem = s.mem) {rs : List Reg}
    (k : Keep rs s t) (h0 : .x0 ∉ rs) : GoodL L t :=
  ⟨hg.1.keep hm k h0, hg.2⟩

/-! ## `double` -/

/-- `double`'s loads. -/
def dblHead (mo acc tmp o : Nat) : List Instr :=
  [ldh .x5 (sArr o), ldh .x10 (sArr mo), ldh .x8 (sArr acc), ldh .x6 (sArr tmp), ldh .x12 sW,
    movi .x7 0, mov .x17 .x5, mov .x16 .x8, mov .x14 .x12, .adds .x .x3 .x7 .x7]

theorem double_eq (mo acc tmp o : Nat) : double mo acc tmp o =
    .seq (.block (dblHead mo acc tmp o))
      (.seq (countLoop .x14 [ld .x3 .x17, .adcs .x .x3 .x3 .x3, st .x3 .x16, next .x17, next .x16])
      (.seq (.block [.adc .x .x3 .x7 .x7, st .x3 .x16]) (.seq subMod selectAcc))) := rfl

/-- After `double`'s loads. -/
def DblHeadL (mo acc tmp o : Nat) (L : Lay) (t : State) : Prop :=
  t.gpr .x5 = off L.B (slot L.w o) ∧ t.gpr .x10 = off L.B (slot L.w mo) ∧
    t.gpr .x8 = off L.B (slot L.w acc) ∧ t.gpr .x6 = off L.B (slot L.w tmp) ∧
    t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x7 = 0 ∧ t.gpr .x17 = off L.B (slot L.w o) ∧
    t.gpr .x16 = off L.B (slot L.w acc) ∧ t.gpr .x14 = BitVec.ofNat 64 L.w

theorem dblHead_ok {L : Lay} {t : State} (hg : GoodL L t) {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8)
    (htmp : tmp < 8) (ho : o < 8) : WP isa (.block (dblHead mo acc tmp o)) t (DblHeadL mo acc tmp o L) := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hg.1.scr.ld (by have := hdr_lt_slot L.w 8 hi; have := hg.2; omega)
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega
  unfold dblHead DblHeadL
  brun [hg.1.x0, hdr_enc (sa o ho), hdr_enc (sa mo hmo), hdr_enc (sa acc hacc), hdr_enc (sa tmp htmp),
    hdr_enc (show sW < 32 by decide), hl _ (sa o ho), hl _ (sa mo hmo), hl _ (sa acc hacc),
    hl _ (sa tmp htmp), hl sW (by decide), hg.1.hdr.harr o ho, hg.1.hdr.harr mo hmo, hg.1.hdr.harr acc hacc,
    hg.1.hdr.harr tmp htmp, hg.1.hdr.hw]

theorem pins_dblHead (mo acc tmp o : Nat) :
    Pins (DblHeadL mo acc tmp o) [.x5, .x10, .x8, .x6, .x12, .x7, .x17, .x16, .x14] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁, i₁, j₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂, i₂, j₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]
  · rw [f₁, f₂]
  · rw [g₁, g₂]
  · rw [i₁, i₂]
  · rw [j₁, j₂]

/-- What `double` does after its loads, checked by the taint analysis. -/
theorem dblTail_ct (mo acc tmp o : Nat) :
    RelCT isa (Two (DblHeadL mo acc tmp o))
      (.seq (countLoop .x14 [ld .x3 .x17, .adcs .x .x3 .x3 .x3, st .x3 .x16, next .x17, next .x16])
      (.seq (.block [.adc .x .x3 .x7 .x7, st .x3 .x16]) (.seq subMod selectAcc))) fun _ _ => True :=
  two_taint _ (pins_dblHead mo acc tmp o) (by taint_decide)

/-- `double` leaks the same in runs with the same working space. -/
theorem double_ct {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.x0]) (.block (dblHead mo acc tmp o)) hc).isSome = true) :
    RelCT isa (Two GoodL) (double mo acc tmp o) fun _ _ => True := by
  rw [double_eq]
  exact RelCT.seq (two_piece _ pins_good h fun _ _ hg => dblHead_ok hg hmo hacc htmp ho)
    (dblTail_ct mo acc tmp o)

/-! ## `doubles` -/

/-- The public data of `doubles`: the working space and the count. -/
structure DblPub where
  L : Lay
  c : Nat

/-- What `doubles` keeps, after `j` doublings. -/
def DblsAt (mo acc tmp o sl : Nat) (p : DblPub) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (O N : Nat), DblsInv σ p.L.B p.L.Z p.L.w p.L.minv mo acc tmp o sl p.c O N j t ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ p.c < 2 ^ 31 ∧ 0 < N

theorem dblsAt_good {mo acc tmp o sl : Nat} {p : DblPub} {j : Nat} {t : State}
    (h : DblsAt mo acc tmp o sl p j t) : GoodL p.L t :=
  let ⟨_, _, _, hI, hZ, _⟩ := h; ⟨⟨hI.scr, hI.x0, hI.hdr⟩, hZ⟩

theorem eval_count {t : State} {j c : Nat} (hj : j < c) (h : (t.gpr .x13).toNat ≠ 0 ↔ j + 1 ≠ c) :
    isa.eval (.nonzero .x .x13) t = some (decide (j + 1 < c)) := by
  rw [eval_nonzero]
  congr 1
  by_cases hc : j + 1 < c
  · have hne : t.gpr .x13 ≠ 0 := fun e => by
      rw [e] at h; exact absurd (h.mpr (by omega)) (by simp)
    rw [bne_iff_ne.mpr hne, decide_eq_true hc]
  · have he : t.gpr .x13 = 0 := BitVec.eq_of_toNat_eq (by
      by_contra hne; exact (h.mp (by simpa using hne)) (by omega))
    rw [he, decide_eq_false hc]; rfl

theorem doubles_eq (mo acc tmp o sl : Nat) : doubles mo acc tmp o sl =
    .seq (.block [sth .x13 sl]) (.loop (.seq (double mo acc tmp o) (.block (dblCount sl))) (.nonzero .x .x13)) :=
  rfl

/-- `doubles` leaks the same in runs with the same working space and count. -/
theorem doubles_ct {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.x0]) (.block (dblHead mo acc tmp o)) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.AArch64.Taint.T}
    (h' : (taint.check (Taint.ofRegs [.x0]) (.block [sth .x13 sl]) hc').isSome = true)
    {hc'' : VG.Taint.Hint VG.AArch64.Taint.T}
    (h'' : (taint.check (Taint.ofRegs [.x0]) (.block (dblCount sl)) hc'').isSome = true) :
    RelCT isa (Two fun (p : DblPub) s => GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ 1 ≤ p.c ∧
      p.c < 2 ^ 31 ∧ s.gpr .x13 = BitVec.ofNat 64 p.c ∧
      wv s.mem p.L.B (slot p.L.w o) p.L.w < wv s.mem p.L.B (slot p.L.w mo) p.L.w)
      (doubles mo acc tmp o sl) (Two fun p s => DblsAt mo acc tmp o sl p p.c s) := by
  rw [doubles_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.c ∧ DblsAt mo acc tmp o sl p 0 s) _
    (fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1) h' ?_) ?_
  · rintro p s ⟨hg, hw, hw', hc1, hc', h13, hO⟩
    exact WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hg.1.scr hg.1.x0 hg.1.hdr hg.2 hmo ho hsl hsl' h13 hO)
      fun t hI => ⟨by omega, s, _, _, hI, hg.2, hw, hw', hc', by omega⟩
  refine two_loop (Φ := DblsAt mo acc tmp o sl) (fun p => p.c) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun (q : DblPub × Nat) s => GoodL q.1.L s)
      (two_map (·.1.L) (fun _ _ h => dblsAt_good h.2) (double_ct hmo hacc htmp ho h)) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_good q.1.L s₁ s₂ h₁ h₂) h'')
    rintro ⟨p, j⟩ s ⟨hj, σ, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (double_ok hI.scr hI.x0 hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7
      (by rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t ⟨_, ha, k⟩ =>
        ⟨⟨hI.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hI.x0, ha.hdr hI.hdr⟩, hZ⟩
  · rintro p j s hj ⟨σ, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (dblIter_ok hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 d8 hsl hsl' hc' hN0 hj hI)
      fun t ⟨hI', hz⟩ => ⟨eval_count hj hz, fun _ => ⟨σ, O, N, hI', hZ, hw, hw', hc', hN0⟩,
        fun e => e ▸ ⟨σ, O, N, hI', hZ, hw, hw', hc', hN0⟩⟩

/-! ## Squarings -/

/-- What a squaring of `[aR2]` needs. -/
def SqPre (L : Lay) (s : State) : Prop :=
  GoodL L s ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31 ∧
    ((word s.mem L.B (slot L.w aN)).toNat * L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem L.B (slot L.w aR2) L.w < wv s.mem L.B (slot L.w aN) L.w

theorem sq_pre (M : Mont) {L : Lay} {s : State} (h : SqPre L s) :
    WP isa (M.mm aR2 aR2 aR2) s (SqPre L) := by
  obtain ⟨hg, hw, hw', hinv, hlt⟩ := h
  have hn' : L.B.toNat + slot L.w 8 ≤ 2 ^ 64 := by have := hg.1.scr.nowrap; have := hg.2; omega
  refine WP.mono (M.mm_ok hg.1 hg.2 hw hw' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hinv hlt) fun t ⟨g, lt, _, ha, _⟩ => ⟨⟨g, hg.2⟩, hw, hw', ?_, ?_⟩
  · rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega)]; exact hinv
  · have hN' : wv t.mem L.B (slot L.w aN) L.w = wv s.mem L.B (slot L.w aN) L.w :=
      ha.wv_of_not_mem (by decide) (by decide) hn'
    rw [hN']; exact lt

theorem sqs_ct (M : Mont) (n : Nat) : RelCT isa (Two SqPre) (seqs (List.replicate (n + 1) (M.mm aR2 aR2 aR2)))
    fun _ _ => True := by
  have one : RelCT isa (Two SqPre) (M.mm aR2 aR2 aR2) fun _ _ => True :=
    two_map id (fun _ _ h => h.1) (M.ctL (.inl ⟨rfl, rfl, rfl⟩))
  induction n with
  | zero => exact one
  | succ n ih =>
    show RelCT isa (Two SqPre) (.seq (M.mm aR2 aR2 aR2) (seqs (List.replicate (n + 1) (M.mm aR2 aR2 aR2)))) _
    exact RelCT.seq (two_post (Ψ := SqPre) one fun _ _ h => sq_pre M h) ih

/-! ## `R² mod m` -/

/-- The public data of `R² mod m`: the working space and `m`. -/
structure R2Pub where
  L : Lay
  N : Nat

/-- The top word of `m`. -/
def R2Pub.top (p : R2Pub) : Nat := p.N / 2 ^ (64 * (p.L.w - 1))

/-- The doublings' count, `64 - j + w` for the top bit `j` of the top word. -/
def R2Pub.cnt (p : R2Pub) : Nat := 64 - p.top.log2 + p.L.w

/-- `r2_ok`'s hypotheses. -/
def R2Pre (p : R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N ∧
    ((word s.mem p.L.B (slot p.L.w aN)).toNat * p.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧ p.N % 2 = 1 ∧
    2 ^ (64 * (p.L.w - 1)) ≤ p.N

theorem R2Pre.keep {p : R2Pub} {s t : State} (h : R2Pre p s) (hm : t.mem = s.mem) {rs : List Reg}
    (k : Keep rs s t) (h0 : .x0 ∉ rs) : R2Pre p t :=
  let ⟨hg, hw, hw', hN, hinv, hodd, hlo⟩ := h
  ⟨hg.keep hm k h0, hw, hw', hm ▸ hN, hm ▸ hinv, hodd, hlo⟩

/-- What the top word of `m` gives. -/
theorem r2top {p : R2Pub} {s : State} (hw : 2 ≤ p.L.w) (hn : wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N)
    (hodd : p.N % 2 = 1) (hlo : 2 ^ (64 * (p.L.w - 1)) ≤ p.N) :
    (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.top ∧ 0 < p.top ∧ p.top < 2 ^ 64 ∧
      p.top.log2 < 64 ∧ 2 ^ p.top.log2 * 2 ^ (64 * (p.L.w - 1)) < p.N := by
  have hsplit : p.N = p.N % 2 ^ (64 * (p.L.w - 1)) +
      2 ^ (64 * (p.L.w - 1)) * (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat := by
    have e : wv s.mem p.L.B (slot p.L.w aN) (p.L.w - 1 + 1) = p.N := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ p.L.w)]; exact hn
    rw [wv] at e
    have hlt := wv_lt s.mem p.L.B (slot p.L.w aN) (p.L.w - 1)
    rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hT : (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.top := by
    unfold R2Pub.top
    have hP := Nat.two_pow_pos (64 * (p.L.w - 1))
    have := Nat.mod_lt p.N hP
    rw [Nat.div_eq_of_lt_le (k := (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat) ?_ ?_]
    · rw [Nat.mul_comm]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
  rw [hT] at hsplit
  have hT0 : 0 < p.top := by
    rcases Nat.eq_zero_or_pos p.top with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at hsplit
      have := Nat.mod_lt p.N (Nat.two_pow_pos (64 * (p.L.w - 1))); omega
    · exact h
  have hT1 : p.top < 2 ^ 64 := hT ▸ BitVec.isLt _
  exact ⟨hT, hT0, hT1, (Nat.log2_lt (by omega)).mpr hT1,
    start_lt hw hodd hsplit (Nat.log2_self_le (n := p.top) (by omega))⟩

theorem R2Pre.top {p : R2Pub} {s : State} (h : R2Pre p s) :
    (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.top ∧ 0 < p.top ∧ p.top < 2 ^ 64 ∧
      p.top.log2 < 64 ∧ 2 ^ p.top.log2 * 2 ^ (64 * (p.L.w - 1)) < p.N :=
  r2top h.2.1 h.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2

theorem pins_r2 {Φ : R2Pub → State → Prop} (h : ∀ p s, Φ p s → R2Pre p s) : Pins Φ [.x0] :=
  fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ (h p s₁ h₁).1 (h p s₂ h₂).1

/-- After `w` and `m`'s base. -/
def R2h (p : R2Pub) (s : State) : Prop :=
  R2Pre p s ∧ s.gpr .x12 = BitVec.ofNat 64 p.L.w ∧ s.gpr .x8 = off p.L.B (slot p.L.w aN)

/-- After the top word's load. -/
def R2a (p : R2Pub) (s : State) : Prop :=
  R2Pre p s ∧ s.gpr .x3 = BitVec.ofNat 64 p.top ∧ s.gpr .x12 = BitVec.ofNat 64 p.L.w

/-- After `topBit`. -/
def R2b (p : R2Pub) (s : State) : Prop :=
  R2Pre p s ∧ s.gpr .x9 = BitVec.ofNat 64 (2 ^ p.top.log2) ∧
    s.gpr .x13 = BitVec.ofNat 64 (64 - p.top.log2) ∧ s.gpr .x12 = BitVec.ofNat 64 p.L.w

/-- Before `setWord`. -/
def R2c (p : R2Pub) (s : State) : Prop :=
  R2Pre p s ∧ s.gpr .x12 = BitVec.ofNat 64 p.L.w ∧ s.gpr .x13 = BitVec.ofNat 64 (p.L.w - 1) ∧
    s.gpr .x9 = BitVec.ofNat 64 (2 ^ p.top.log2) ∧
    word s.mem p.L.B (8 * sCnt) = BitVec.ofNat 64 (64 - p.top.log2)

/-- After the start, `2^(b - 1)`. -/
def R2d (p : R2Pub) (s : State) : Prop :=
  R2Pre p s ∧ word s.mem p.L.B (8 * sCnt) = BitVec.ofNat 64 (64 - p.top.log2) ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ p.top.log2 * 2 ^ (64 * (p.L.w - 1))

/-- Before the doublings. -/
def R2e (p : R2Pub) (s : State) : Prop :=
  R2d p s ∧ s.gpr .x13 = BitVec.ofNat 64 p.cnt

theorem setWord_eq (o : Nat) : setWord o =
    .seq (.block [ldh .x8 (sArr o), movi .x7 0]) (.seq zeroAcc
      (.block [.lsl .x .x16 .x13 3, .add .x .x16 .x8 .x16, st .x9 .x16])) := rfl

/-- `R² mod m` leaks the same in runs that agree on `m`. -/
theorem r2_ct (M : Mont) : RelCT isa (Two R2Pre) (seqs (r2Steps M.mm)) fun _ _ => True := by
  rw [r2Steps_eq]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (R := Two SqPre) ?_ (sqs_ct M 5))
  -- `w` and `m`'s base.
  refine RelCT.seq (RelCT.block_append (l₁ := ([ldh .x12 sW, ldh .x8 (sArr aN)] : List Instr))
    (l₂ := ([.subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x8 .x4, ld .x3 .x4] : List Instr))
    (RelCT.seq (two_piece (Ψ := R2h) _ (pins_r2 fun _ _ h => h) (by taint_decide) ?_)
      (two_piece (Ψ := R2a) [.x12, .x8] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide) ?_))) ?_
  · intro p s h
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      h.1.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := h.1.2; omega)
    refine WP.mono (WP.keep [.x8, .x12] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 p.L.w ∧
        t.gpr .x8 = off p.L.B (slot p.L.w aN) ∧ t.mem = s.mem) (by
      brun [h.1.1.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide), hl sW (by decide),
        hl (sArr aN) (by decide), h.1.1.hdr.hw, h.1.1.hdr.harr aN (by decide)])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h12, h8, hm⟩, k⟩ => ⟨h.keep hm k (by decide), h12, h8⟩
  -- The top word.
  · intro p s ⟨h, h12, h8⟩
    obtain ⟨hT, -⟩ := h.top
    have hn := h.1.1.scr.nowrap
    have hw2 := h.2.1
    have := slot_le (w := p.L.w) (show aN < 8 by decide)
    have hw8 : (BitVec.ofNat 64 p.L.w - BitVec.ofNat 64 1) <<< 3 = BitVec.ofNat 64 (8 * (p.L.w - 1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 p.top ∧
        t.gpr .x12 = BitVec.ofNat 64 p.L.w ∧ t.mem = s.mem) (by
      brun [h12, h8, hw8, off_add,
        h.1.1.scr.ld (show slot p.L.w aN + 8 * (p.L.w - 1) + 8 ≤ p.L.Z by have := h.1.2; omega)]
      rw [← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h3, h12', hm⟩, k⟩ => ⟨h.keep hm k (by decide), h3, h12'⟩
  -- Its top bit.
  refine RelCT.seq (two_piece (Ψ := R2b) [.x3] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · intro p s ⟨h, h3, h12⟩
    obtain ⟨-, hT0, hT1, -⟩ := h.top
    exact WP.mono (topBit_ok h3 hT0 hT1) fun t ⟨⟨h9, h13, hm⟩, k⟩ =>
      ⟨h.keep hm k (by decide), h9, h13, (k.gpr .x12 (by decide)).trans h12⟩
  -- The count into the header, and the start's word index.
  refine RelCT.seq (two_piece (Ψ := R2c) _ (pins_r2 fun _ _ h => h.1) (by taint_decide) ?_) ?_
  · intro p s ⟨⟨hg, hw, hw', hN, hinv, hodd, hlo⟩, h9, h13, h12⟩
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
  -- The start.
  refine RelCT.seq (two_post (Ψ := R2d) ?_ ?_) ?_
  · rw [setWord_eq]
    refine RelCT.seq (two_piece (Ψ := fun p s => R2c p s ∧ s.gpr .x8 = off p.L.B (slot p.L.w aR2) ∧
        s.gpr .x7 = 0) _ (pins_r2 fun _ _ h => h.1) (by taint_decide) fun p s h => ?_)
      (two_taint [.x8, .x12, .x13, .x7] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.1.2.1, h₂.1.2.1]
        · rw [h₁.1.2.2.1, h₂.1.2.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    have hl : InRegions (s.rd ++ s.wr) (off p.L.B (8 * sArr aR2)) 8 :=
      h.1.1.1.scr.ld (by have := hdr_lt_slot p.L.w 8 (show sArr aR2 < 32 by decide); have := h.1.1.2; omega)
    refine WP.mono (WP.keep [.x7, .x8] (Q := fun t => t.gpr .x8 = off p.L.B (slot p.L.w aR2) ∧ t.gpr .x7 = 0 ∧
        t.mem = s.mem) (by
      brun [h.1.1.1.x0, hdr_enc (show sArr aR2 < 32 by decide), hl, h.1.1.1.hdr.harr aR2 (by decide)])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h8, h7, hm⟩, k⟩ => ⟨?_, h8, h7⟩
    obtain ⟨hr, h12, h13, h9, hcnt⟩ := h
    exact ⟨hr.keep hm k (by decide), (k.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13,
      (k.gpr .x9 (by decide)).trans h9, hm ▸ hcnt⟩
  · intro p s ⟨⟨hg, hw, hw', hN, hinv, hodd, hlo⟩, h12, h13, h9, hcnt⟩
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
  -- The count of doublings.
  refine RelCT.seq (two_piece (Ψ := R2e) _ (pins_r2 fun _ _ h => h.1) (by taint_decide) ?_) ?_
  · intro p s h
    obtain ⟨hr, hcnt, hv⟩ := h
    have hg := hr.1
    have h0 := hdr_lt_slot p.L.w 0 (show 31 < 32 by decide)
    have h0' := slot_le (w := p.L.w) (show 0 < 8 by decide)
    have := hg.2
    refine WP.mono (WP.keep [.x12, .x13] (Q := fun t => t.gpr .x13 = BitVec.ofNat 64 p.cnt ∧ t.mem = s.mem) (by
      brun [hg.1.x0, hdr_enc (show sCnt < 32 by decide), hdr_enc (show sW < 32 by decide),
        hg.1.scr.ld (d := 8 * sCnt) (by unfold sCnt sFn; omega), hg.1.scr.ld (d := 8 * sW) (by unfold sW; omega),
        hcnt, hg.1.hdr.hw, ← BitVec.ofNat_add]
      rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h13, hm⟩, k⟩ =>
        ⟨⟨hr.keep hm k (by decide), hm ▸ hcnt, hm ▸ hv⟩, h13⟩
  -- The doublings.
  refine RelCT.mono (two_post (Ψ := fun (p : R2Pub) s => SqPre p.L s) ((two_map (fun p => (⟨p.L, p.cnt⟩ : DblPub))
    (fun p s h => ?_) (doubles_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide)
      (by taint_decide) (by taint_decide))).mono (fun _ _ h => h) fun _ _ _ => trivial) ?_) (fun _ _ h => h)
    (fun _ _ ⟨p, h₁, h₂, hsp⟩ => ⟨p.L, h₁, h₂, hsp⟩)
  · obtain ⟨⟨⟨hg, hw, hw', hN, -, hodd, hlo⟩, -, hv⟩, h13⟩ := h
    obtain ⟨-, -, -, hL, hv0⟩ := r2top (s := s) hw hN hodd hlo
    exact ⟨hg, hw, show p.L.w < 2 ^ 31 by omega, show 1 ≤ p.cnt by unfold R2Pub.cnt; omega,
      show p.cnt < 2 ^ 31 by unfold R2Pub.cnt; omega, h13, by rw [hv, hN]; exact hv0⟩
  · intro p s h
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

end VG.Proof.Bignum.AArch64
