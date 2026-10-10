import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Win
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas

/-!
# RSA with AVX512_IFMA on x86-64, any size: the exponentiations

`expLoop` builds the table, then for each of the
`E = 8 W` bytes of the exponents (at `oE` of each region, most significant
first) puts the byte in the top 8 bits of `V` (`ldV_ok`) and does two
windows (`wins_ok`): `Y ≡ x^E R` becomes `x^(256 E + b) R`. After all of
them `Y ≡ x^e R`, `e` the exponent (`ev`), from `Y ≡ R` (`expLoop_ok`).
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (wp_seqs_app ror8_byte ror60_v ea_idx r14Dec_ok vj win_exp ofs_off0 se_ofNat)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The first `i` bytes of prime `p`'s exponent, big-endian. -/
def ev (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (p : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ev l m B p i * 256 + (m (off B (l.D * p + l.oE + i))).toNat

theorem nib_hi {m : Mem} {B : Addr} {p b : Nat} (hb : b < 256)
    (h : word m B (l.D * p + l.oV) = BitVec.ofNat 64 (b * 2 ^ 56)) : nib l m B p = b / 16 := by
  unfold nib; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])]; omega_using []

theorem nib_lo {m : Mem} {B : Addr} {p b : Nat} (hb : b < 256)
    (h : word m B (l.D * p + l.oV) = BitVec.ofNat 64 (b % 16 * 2 ^ 60 + b / 16)) : nib l m B p = b % 16 := by
  unfold nib; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])]; omega_using [hb]

/-- The byte `i` of prime `p`'s exponent. -/
abbrev ebyte (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (p i : Nat) : Nat := (m (off B (l.D * p + l.oE + i))).toNat

/-- Byte `i` of prime `p`'s exponent into the top 8 bits of `V`. -/
theorem ldV_ok {s : State} {B : Addr} {p i : Nat} (hp : p < 2) (hi : i < l.E)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hs : Scr s B (2 * l.D)) :
    WP isa (.block [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * p + l.oE : Nat) : Int) },
        .shift .ror .rax 8, .store (at_ .rbx (l.D * p + l.oV)) .rax]) s fun s' =>
      s'.mem = s.mem.writeW (off B (l.D * p + l.oV)) (BitVec.ofNat 64 (ebyte l s.mem B p i * 2 ^ 56)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  have e : B + BitVec.ofNat 64 i + BitVec.ofNat 64 (l.D * p + l.oE) = off B (l.D * p + l.oE + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm i]
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 i + BitVec.ofNat 64 (l.D * p + l.oE)) 1 := by
    rw [e]
    obtain ⟨r, h, c⟩ := hs.region (d := l.D * p + l.oE + i) (n := 1) (by omega_using [hi, o6, o10, hDp]) (by decide)
    exact ⟨r, List.mem_append_right _ h, c⟩
  have hst : InRegions s.wr (B + BitVec.ofNat 64 (l.D * p + l.oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region (d := l.D * p + l.oV) (n := 8) (by omega_using [o8, o10, hDp]) (by decide); ⟨_, h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' =>
    s'.mem = s.mem.writeW (off B (l.D * p + l.oV)) (BitVec.ofNat 64 (ebyte l s.mem B p i * 2 ^ 56)) ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [ea_idx, eaG', hB, h13, hld, hst, ror8_byte]
    rw [e]
    and_intros <;> rfl) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

/-- After `j` windows of the bytes `bs`, from `t₀` where `Y ≡ x^E R`. -/
structure WinInv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (t₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (E bs : Nat → Nat) (j : Nat)
    (t : State) : Prop where
  r14 : t.gpr .r14 = BitVec.ofNat 64 (2 - j)
  st : ExpSt l t.mem B M k x Q (fun p => E p * 16 ^ j + bs p / 16 ^ (2 - j))
  v : j < 2 → ∀ p < 2, word t.mem B (l.D * p + l.oV) = BitVec.ofNat 64 (vj (bs p) j)
  frame : OutW l B t₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r14 → r ≠ .r15 → t.gpr r = t₀.gpr r
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  mxcsr : t.mxcsr = t₀.mxcsr

/-- Window `j` of the bytes `bs`. -/
theorem winStep_ok (hl : LayOk l) {t₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E bs : Nat → Nat}
    {j : Nat} (hj : j < 2) (hbs : ∀ p < 2, bs p < 256) (hB : t₀.gpr .rbx = B) (hs : Scr t₀ B (2 * l.D))
    (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p)) (h : WinInv l t₀ B M k x Q E bs j t) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (window l ++ ([.block [.alu .sub .r14 (.imm 1)]] : List (Prog isa)))) t
      fun t' => WinInv l t₀ B M k x Q E bs (j + 1) t' ∧ t'.zf = some (decide (j + 1 = 2)) := by
  have hBt : t.gpr .rbx = B := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hB
  refine wp_seqs_app (by simp [window]) (by simp)
    (WP.mono (window_ok hl hBt (hs.congr h.wr) hR h.st) fun t₁ ⟨st₁, v₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have r14₁ : t₁.gpr .r14 = BitVec.ofNat 64 (2 - j) := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.r14
  refine WP.mono (r14Dec_ok (n := 2 - j) (by omega_using [hj]) (by omega_using []) r14₁) fun t₂ ⟨r14₂, z₂, k₂, me₂, x₂⟩ =>
    ⟨⟨by rw [r14₂, show 2 - j - 1 = 2 - (j + 1) by omega_arith], ?_, fun hj' p hp => ?_,
      by rw [me₂]; exact h.frame.trans f₁,
      fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 => ?_, by rw [k₂.2.1, rd₁, h.rd], by rw [k₂.2.2, wr₁, h.wr],
      by rw [x₂, x₁, h.mxcsr]⟩, by rw [z₂]; congr 1; exact decide_eq_decide.mpr (by omega_using [hj])⟩
  · rw [me₂]
    refine ⟨st₁.ar, st₁.tab, st₁.y, fun hq p hp => ?_⟩
    rw [st₁.yv hq p hp, win_exp (hbs p hp) hj _ ?_]
    have hv := h.v hj p hp
    unfold vj at hv
    rcases (show j = 0 ∨ j = 1 by omega_using [hj]) with rfl | rfl
    · rw [nib_hi (hbs p hp) hv]; rfl
    · rw [nib_lo (hbs p hp) hv]; rfl
  · rw [me₂, v₁ p hp, h.v hj p hp]
    rcases (show j = 0 by omega_using [hj']) with rfl
    unfold vj
    simp only [ite_true]
    exact ror60_v _ (hbs p hp)
  · rw [k₂.gpr (by simp [r10]), g₁ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r11]
    exact h.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11

/-- The two windows of the bytes `bs`. -/
theorem winLoop_ok (hl : LayOk l) {t₀ : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E bs : Nat → Nat}
    (hbs : ∀ p < 2, bs p < 256) (hB : t₀.gpr .rbx = B) (hs : Scr t₀ B (2 * l.D))
    (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p)) {t : State} (h : WinInv l t₀ B M k x Q E bs 0 t) :
    WP isa (.loop (VG.Impl.Bignum.X86_64.seqs (window l ++
      ([.block [.alu .sub .r14 (.imm 1)]] : List (Prog isa)))) .ne) t (WinInv l t₀ B M k x Q E bs 2) := by
  refine WP.loop (M := isa) (c := .ne) (Q := WinInv l t₀ B M k x Q E bs 2)
    (fun n t => 1 ≤ n ∧ n ≤ 2 ∧ WinInv l t₀ B M k x Q E bs (2 - n) t) ?_ 2 t
    ⟨by decide, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  intro n t ⟨h1, h2, hI⟩
  refine WP.mono (winStep_ok hl (by omega_using [h1]) hbs hB hs hR hI) fun t' ⟨hI', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · exact .inl ⟨by simp, hI'⟩
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (2 - n + 1 = 2) by omega_using [hn]), Bool.not_false], n - 1,
      by omega_using [hn], by omega_using [hn], by omega_using [h2], by rw [show 2 - (n - 1) = 2 - n + 1 by omega_using [h2, hn]]; exact hI'⟩

/-- The exponents' bytes outside `Y`, `S` and `V`. -/
theorem OutW.byte (hl : LayOk l) {B : Addr} {m m' : Mem} (h : OutW l B m m') {p i : Nat} (hp : p < 2)
    (hi : i < l.E) : m' (off B (l.D * p + l.oE + i)) = m (off B (l.D * p + l.oE + i)) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  refine h _ fun p' hp' => ?_
  rw [ofs_off0 B (by omega_using [hi, o6, o10, hD, hDp])]
  rcases D_mul (l := l) hp with h1 | h1 <;> rcases D_mul (l := l) hp' with h2 | h2 <;> omega_using [hi, o2, o4, o6, o8, h1, h2, o10]

/-- The next byte, `ZF` after the last. -/
theorem r13Inc_ok (hl : LayOk l) {s : State} {i : Nat} (hi : i < l.E) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm (BitVec.ofNat 32 l.E))]) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (i + 1) ∧ s'.zf = some (decide (i + 1 = l.E)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r13] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hE : l.E < 2 ^ 31 := by
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
    have := hl.D_bounds; omega_arith
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun s' =>
    s'.gpr .r13 = BitVec.ofNat 64 (i + 1) ∧ s'.zf = some (decide (i + 1 = l.E)) ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [h13, se_ofNat hE, ofNat_add_one]
    and_intros
    · rw [ofNat_sub_beq (by omega_using [hi, hE]) (by omega_using [hE])]
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, k, c, d⟩

theorem ExpSt.of_outV (hl : LayOk l) {m m' : Mem} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (h : ExpSt l m B M k x Q E) (f : Out2 l B l.oV 8 m m') : ExpSt l m' B M k x Q E := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  exact ⟨h.ar.of_out2 hl f (by omega_using [o2, o8]) (by omega_using [o8, o10]),
      h.tab_of hl f (.inr (by omega_using [o5, o8])) (by omega_using [o8, o10]),
    fun p hp => (h.y p hp).of_out2 hl hp f (.inl (by omega_using [o2, o8])) (by omega_using [o2, o10]) (by omega_using [o8, o10]),
    fun hq p hp => by rw [f.val hl hp (.inl (by omega_using [o2, o8])) (by omega_using [o2, o10]) (by omega_using [o8, o10])]; exact h.yv hq p hp⟩

theorem ExpSt.congrE {m : Mem} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E E' : Nat → Nat}
    (h : ExpSt l m B M k x Q E) (e : ∀ p < 2, E p = E' p) : ExpSt l m B M k x Q E' :=
  ⟨h.ar, h.tab, h.y, fun hq p hp => by rw [← e p hp]; exact h.yv hq p hp⟩

/-- After the bytes below `i` of the exponents, from `t₀`. -/
structure ByteInv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (t₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (i : Nat) (t : State) :
    Prop where
  r13 : t.gpr .r13 = BitVec.ofNat 64 i
  st : ExpSt l t.mem B M k x Q (fun p => ev l t₀.mem B p i)
  frame : OutW l B t₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → t.gpr r = t₀.gpr r
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  mxcsr : t.mxcsr = t₀.mxcsr

/-- The body of the loop over the bytes. -/
def byteBody (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prog isa :=
  VG.Impl.Bignum.X86_64.seqs [.block ((List.range 2).flatMap fun p =>
      [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * p + l.oE : Nat) : Int) },
        .shift .ror .rax 8, .store (at_ .rbx (l.D * p + l.oV)) .rax]),
    .block [.mov32 .r14 (.imm 2)],
    .loop (VG.Impl.Bignum.X86_64.seqs (window l ++ ([.block [.alu .sub .r14 (.imm 1)]] : List (Prog isa)))) .ne,
    .block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm (BitVec.ofNat 32 l.E))]]

/-- The byte `i` of both exponents. -/
theorem byteIter_ok (hl : LayOk l) {t₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {i : Nat}
    (hi : i < l.E) (hB : t₀.gpr .rbx = B) (hs : Scr t₀ B (2 * l.D))
    (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p)) (h : ByteInv l t₀ B M k x Q i t) :
    WP isa (byteBody l) t fun t' => ByteInv l t₀ B M k x Q (i + 1) t' ∧ t'.zf = some (decide (i + 1 = l.E)) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hn := hs.nowrap
  have hBt : t.gpr .rbx = B := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hB
  have hst : Scr t B (2 * l.D) := hs.congr h.wr
  refine WP.seq ?_
  rw [show ((List.range 2).flatMap fun p =>
      ([.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * p + l.oE : Nat) : Int) },
        .shift .ror .rax 8, .store (at_ .rbx (l.D * p + l.oV)) .rax] : List Instr)) =
      ([.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * 0 + l.oE : Nat) : Int) },
        .shift .ror .rax 8, .store (at_ .rbx (l.D * 0 + l.oV)) .rax] : List Instr) ++
      [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * 1 + l.oE : Nat) : Int) },
        .shift .ror .rax 8, .store (at_ .rbx (l.D * 1 + l.oV)) .rax] from rfl,
    WP.block_append_iff]
  refine WP.mono (ldV_ok (p := 0) (by decide) hi hBt h.r13 hst) fun t₁ ⟨m₁, k₁, x₁⟩ => ?_
  refine WP.mono (ldV_ok (p := 1) (by decide) hi (by rw [k₁.gpr (by decide)]; exact hBt)
    (by rw [k₁.gpr (by decide)]; exact h.r13) (hst.congr k₁.2.2)) fun t₂ ⟨m₂, k₂, x₂⟩ => ?_
  have o₁ : Outside B (l.D * 0 + l.oV) 8 t.mem t₁.mem := by rw [m₁]; exact writeW_outside _ B _ (by omega_using [o8, o10, hn])
  have o₂ : Outside B (l.D * 1 + l.oV) 8 t₁.mem t₂.mem := by rw [m₂]; exact writeW_outside _ B _ (by omega_using [o8, o10, hn])
  have fV : Out2 l B l.oV 8 t.mem t₂.mem :=
    (Out2.of_outside (p := 0) (by decide) o₁).trans (Out2.of_outside (p := 1) (by decide) o₂)
  let bs : Nat → Nat := fun p => ebyte l t₀.mem B p i
  have hbs : ∀ p < 2, bs p < 256 := fun p _ => (t₀.mem (off B (l.D * p + l.oE + i))).isLt
  have b0 : ebyte l t.mem B 0 i = bs 0 := by
    show (t.mem _).toNat = (t₀.mem _).toNat; rw [h.frame.byte hl (by decide) hi]
  have b1 : ebyte l t₁.mem B 1 i = bs 1 := by
    show (t₁.mem _).toNat = (t₀.mem _).toNat
    rw [o₁ _ (by rw [ofs_off0 B (by omega_using [hi, o6, o10, hn])]; omega_using [o8, o10]), h.frame.byte hl (by decide) hi]
  rw [b0] at m₁
  rw [b1] at m₂
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨t₂.setReg32 .r14 2, rfl, WP.block_nil ?_⟩
  generalize hu : t₂.setReg32 .r14 2 = u
  have eu : u.mem = t₂.mem ∧ u.rd = t₂.rd ∧ u.wr = t₂.wr ∧ u.mxcsr = t₂.mxcsr ∧
      u.gpr .r14 = BitVec.ofNat 64 2 ∧ ∀ r, r ≠ .r14 → u.gpr r = t₂.gpr r := by
    rw [← hu]
    exact ⟨rfl, rfl, rfl, rfl, by rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl,
      fun r hr => by rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr]⟩
  obtain ⟨mu, rdu, wru, xu, r14u, gu⟩ := eu
  have hBu : u.gpr .rbx = B := by rw [gu _ (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]; exact hBt
  have hsu : Scr u B (2 * l.D) := hst.congr (by rw [wru, k₂.2.2, k₁.2.2])
  have i₀ : WinInv l u B M k x Q (fun p => ev l t₀.mem B p i) bs 0 u := by
    refine ⟨r14u, ?_, fun _ p hp => ?_, OutW.refl _ _, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
    · rw [mu]
      exact (h.st.of_outV hl fV).congrE fun p hp => by
        have := hbs p hp
        simp only [Nat.pow_zero, Nat.mul_one, Nat.sub_zero]; omega_using [this]
    · rw [mu]
      show _ = BitVec.ofNat 64 (bs p * 2 ^ 56)
      rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl
      · rw [o₂.word (by omega_using [o10]) (by omega_using [o8, o10, hn]), m₁, VG.Proof.Bignum.word_writeW_self]
      · rw [m₂, VG.Proof.Bignum.word_writeW_self]
  refine WP.seq (WP.mono (winLoop_ok hl hbs hBu hsu hR i₀) fun t₃ w₃ => ?_)
  have r13₃ : t₃.gpr .r13 = BitVec.ofNat 64 i := by
    rw [w₃.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), gu _ (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]; exact h.r13
  refine WP.mono (r13Inc_ok hl hi r13₃) fun t₄ ⟨r13₄, z₄, k₄, me₄, x₄⟩ =>
    ⟨⟨r13₄, ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 => ?_, ?_, ?_, ?_⟩, z₄⟩
  · rw [me₄]
    exact w₃.st.congrE fun p hp => by simp only [ev, Nat.sub_self, Nat.pow_zero, Nat.div_one]; rfl
  · rw [me₄]; exact (h.frame.trans (OutW.ofV fV)).trans (mu ▸ w₃.frame)
  · rw [k₄.gpr (by simp [r10]), w₃.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r11 r12, gu r r11, k₂.gpr (by simp [r1]),
      k₁.gpr (by simp [r1])]
    exact h.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  · rw [k₄.2.1, w₃.rd, rdu, k₂.2.1, k₁.2.1, h.rd]
  · rw [k₄.2.2, w₃.wr, wru, k₂.2.2, k₁.2.2, h.wr]
  · rw [x₄, w₃.mxcsr, xu, x₂, x₁, h.mxcsr]

/-- The loop over the bytes, from byte `E - n`. -/
theorem byteLoop_ok (hl : LayOk l) {t₀ : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop}
    (hB : t₀.gpr .rbx = B) (hs : Scr t₀ B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p)) :
    ∀ n t, 1 ≤ n → n ≤ l.E → ByteInv l t₀ B M k x Q (l.E - n) t →
      WP isa (.loop (byteBody l) .ne) t (ByteInv l t₀ B M k x Q l.E) := by
  intro n t h1 hE hI
  refine WP.loop (M := isa) (c := .ne) (Q := ByteInv l t₀ B M k x Q l.E)
    (fun n t => 1 ≤ n ∧ n ≤ l.E ∧ ByteInv l t₀ B M k x Q (l.E - n) t) ?_ n t ⟨h1, hE, hI⟩
  intro n t ⟨h1, hE, hI⟩
  refine WP.mono (byteIter_ok hl (i := l.E - n) (by omega_using [h1, hE]) hB hs hR hI) fun t' ⟨hI', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · exact .inl ⟨by simp only [show l.E - 1 + 1 = l.E by omega_using [hE], decide_true, Bool.not_true], by
      rw [show l.E - 1 + 1 = l.E by omega_using [hE]] at hI'; exact hI'⟩
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (l.E - n + 1 = l.E) by omega_using [hE, hn]), Bool.not_false], n - 1,
      by omega_using [hn], by omega_using [hn], by omega_using [hE], by rw [show l.E - (n - 1) = l.E - n + 1 by omega_using [hE, hn]]; exact hI'⟩

theorem ev_congr {m m' : Mem} {B : Addr} {p : Nat} :
    ∀ n, (∀ i < n, m' (off B (l.D * p + l.oE + i)) = m (off B (l.D * p + l.oE + i))) →
      ev l m' B p n = ev l m B p n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [ev]; rw [ev_congr n fun i hi => h i (by omega_using [hi]), h n (by omega_using [])]

/-- `m'` agrees with `m` but on `Y`, `S`, `V` and the table of each region. -/
def OutE (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (m m' : Mem) : Prop :=
  ∀ a, (∀ p < 2, (ofs B a < l.D * p + l.oY ∨ l.D * p + l.oY + l.NB ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oS ∨ l.D * p + l.oS + l.NB ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oV ∨ l.D * p + l.oV + 8 ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oTab ∨ l.D * p + l.oTab + 16 * l.NB ≤ ofs B a)) → m' a = m a

theorem OutE.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : OutE l B m₁ m₂) (h₂ : OutE l B m₂ m₃) : OutE l B m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem OutE.ofW {B : Addr} {m m' : Mem} (h : OutW l B m m') : OutE l B m m' :=
  fun a ha => h a fun p hp => ⟨(ha p hp).1, (ha p hp).2.1, (ha p hp).2.2.1⟩

theorem OutE.ofT {B : Addr} {m m' : Mem} (h : Out2 l B l.oTab (16 * l.NB) m m') : OutE l B m m' :=
  fun a ha => h a fun p hp => (ha p hp).2.2.2

theorem E_pos (hl : LayOk l) : 1 ≤ l.E := by rcases hl with rfl | rfl | rfl <;> decide

/-- The exponentiations: `Y ≡ x^e R` for the exponents `e`, from `Y ≡ R` and `X ≡ x R`. -/
theorem expLoop_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * l.D)) (ar : Ar l s.mem B M k) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p))
    (gy : ∀ p < 2, Good l s.mem B M l.oY p) (gx : ∀ p < 2, Good l s.mem B M l.oX p)
    (vy : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oY) % M p = x p ^ 0 * 2 ^ (52 * l.L) % M p)
    (vx : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oX) % M p = x p ^ 1 * 2 ^ (52 * l.L) % M p) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (expLoop l)) s fun s' =>
      ExpSt l s'.mem B M k x Q (fun p => ev l s.mem B p l.E) ∧ OutE l B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  refine wp_seqs_app (by simp [tabBuild]) (by simp)
    (WP.mono (tabBuild_ok hl hB hs ar hR gy gx vy vx) fun s₁ t₁ => ?_)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁.setReg32 .r13 0, rfl, WP.block_nil ?_⟩
  generalize hu : s₁.setReg32 .r13 0 = u
  have eu : u.mem = s₁.mem ∧ u.rd = s₁.rd ∧ u.wr = s₁.wr ∧ u.mxcsr = s₁.mxcsr ∧
      u.gpr .r13 = BitVec.ofNat 64 0 ∧ ∀ r, r ≠ .r13 → u.gpr r = s₁.gpr r := by
    rw [← hu]
    exact ⟨rfl, rfl, rfl, rfl, by rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl,
      fun r hr => by rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr]⟩
  obtain ⟨mu, rdu, wru, xu, r13u, gu⟩ := eu
  have hBu : u.gpr .rbx = B := by rw [gu _ (by decide)]; exact t₁.rbx
  have hsu : Scr u B (2 * l.D) := hs.congr (by rw [wru, t₁.wr])
  have st₀ : ExpSt l u.mem B M k x Q (fun p => ev l u.mem B p (l.E - l.E)) := by
    rw [mu, Nat.sub_self]
    refine ⟨t₁.ar, t₁.tab, fun p hp => (gy p hp).of_out2 hl hp t₁.frame (.inl (by omega_using [o2, o5]))
        (by omega_using [o2, o10]) (by omega_using [o5, o10]),
      fun hq p hp => ?_⟩
    rw [t₁.frame.val hl hp (.inl (by omega_using [o2, o5])) (by omega_using [o2, o10]) (by omega_using [o5, o10])]
    exact vy hq p hp
  refine WP.mono (byteLoop_ok hl hBu hsu hR l.E u (E_pos hl) (Nat.le_refl _)
    ⟨by rw [Nat.sub_self]; exact r13u, st₀, OutW.refl _ _, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s' b' => ?_
  have hev : ∀ p < 2, ev l u.mem B p l.E = ev l s.mem B p l.E := fun p hp => by
    rw [mu]
    refine ev_congr l.E fun i hi => t₁.frame _ fun p' hp' => ?_
    have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
    rw [ofs_off0 B (by have := hs.nowrap; omega_using [o6, o10, hi, hDp, this])]
    rcases D_mul (l := l) hp with h1 | h1 <;> rcases D_mul (l := l) hp' with h2 | h2 <;> omega_using [o5, o6, h2, o10, hi, h1]
  refine ⟨b'.st.congrE hev, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 => ?_, ?_, ?_, ?_⟩
  · exact (OutE.ofT t₁.frame).trans (mu ▸ OutE.ofW b'.frame)
  · rw [b'.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12, gu r r10]
    exact t₁.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  · rw [b'.rd, rdu, t₁.rd]
  · rw [b'.wr, wru, t₁.wr]
  · rw [b'.mxcsr, xu, t₁.mxcsr]

end VG.Proof.Bignum.X86_64.Ifma
