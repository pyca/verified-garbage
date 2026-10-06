import VerifiedGarbage.Proof.Bignum.X86_64.G.Tab
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaWin

/-!
# RSA with AVX512_IFMA on x86-64, any size: a window of the exponentiations

`IfmaWin` for `CrtIfmaG`. `ExpSt`: the regions' moduli (`Ar`), the table
(`T_j ≡ x^j R`) and `Y ≡ x^E R` for each prime, `R = 2^(208 R)`. A window
(`window_ok`) squares `Y` four times (`sq_ok`), reads `T_v` into `S` for
the top 4 bits `v` of each prime's quadword at `oV` (`select_ok`), rotates
that quadword up by 4 bits, and multiplies `Y` by `S` (`mulS_ok`):
`Y ≡ x^(16 E + v) R`. It writes only `Y`, `S` and `V` of each region
(`OutW`).
-/

namespace VG.Proof.Bignum.X86_64.G

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfmaG
open VG.Proof.Bignum.X86_64.AmmSym (mont_mul2 r15Dec_ok ea_at' wp_seqs_app)

variable {l : Lay}

/-- The state of the exponentiations: `Y ≡ x^E R`. -/
structure ExpSt (l : Lay) (m : Mem) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (E : Nat → Nat) : Prop where
  ar : Ar l m B M k
  tab : ∀ j < 16, ∀ p < 2, Good l m B M (l.oTab + l.NB * j) p ∧
    (Q → val52 l m B (l.D * p + (l.oTab + l.NB * j)) % M p = x p ^ j * 2 ^ (52 * l.L) % M p)
  y : ∀ p < 2, Good l m B M l.oY p
  yv : Q → ∀ p < 2, val52 l m B (l.D * p + l.oY) % M p = x p ^ E p * 2 ^ (52 * l.L) % M p

/-- `m'` agrees with `m` but on `Y`, `S` and `V` of each region. -/
def OutW (l : Lay) (B : Addr) (m m' : Mem) : Prop :=
  ∀ a, (∀ p < 2, (ofs B a < l.D * p + l.oY ∨ l.D * p + l.oY + l.NB ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oS ∨ l.D * p + l.oS + l.NB ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oV ∨ l.D * p + l.oV + 8 ≤ ofs B a)) →
    m' a = m a

theorem OutW.refl (B : Addr) (m : Mem) : OutW l B m m := fun _ _ => rfl

theorem OutW.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : OutW l B m₁ m₂) (h₂ : OutW l B m₂ m₃) : OutW l B m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem OutW.ofY {B : Addr} {m m' : Mem} (h : Out2 l B l.oY l.NB m m') : OutW l B m m' :=
  fun a ha => h a fun p hp => (ha p hp).1

theorem OutW.ofS {B : Addr} {m m' : Mem} (h : Out2 l B l.oS l.NB m m') : OutW l B m m' :=
  fun a ha => h a fun p hp => (ha p hp).2.1

theorem OutW.ofV {B : Addr} {m m' : Mem} (h : Out2 l B l.oV 8 m m') : OutW l B m m' :=
  fun a ha => h a fun p hp => (ha p hp).2.2

/-- The table after a write elsewhere. -/
theorem ExpSt.tab_of (hl : LayOk l) {m m' : Mem} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (h : ExpSt l m B M k x Q E) {o n : Nat} (hf : Out2 l B o n m m')
    (ho : o + n ≤ l.oTab ∨ l.oTab + 16 * l.NB ≤ o) (hoD : o + n ≤ l.D) :
    ∀ j < 16, ∀ p < 2, Good l m' B M (l.oTab + l.NB * j) p ∧
      (Q → val52 l m' B (l.D * p + (l.oTab + l.NB * j)) % M p = x p ^ j * 2 ^ (52 * l.L) % M p) :=
  fun j hj p hp => by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hNj : l.NB * j + l.NB ≤ 16 * l.NB := by
    rw [← Nat.mul_succ, Nat.mul_comm 16]; exact Nat.mul_le_mul_left _ hj
  have hc : l.oTab + l.NB * j + l.NB ≤ o ∨ o + n ≤ l.oTab + l.NB * j := by
    rcases ho with ho | ho
    · exact .inr (by omega)
    · exact .inl (by omega)
  have hcD : l.oTab + l.NB * j + l.NB ≤ l.D := by omega
  obtain ⟨g, v⟩ := h.tab j hj p hp
  exact ⟨g.of_out2 hl hp hf hc hcD hoD, fun hq => by rw [hf.val hl hp hc hcD hoD]; exact v hq⟩

/-- `Y := Y² / R`: `x^E R` becomes `x^(2E) R`. -/
theorem sq_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p))
    (h : ExpSt l s.mem B M k x Q E) :
    WP isa (amm l l.oY l.oY l.oY) s fun s' => ExpSt l s'.mem B M k x Q (fun p => 2 * E p) ∧
      Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.mono (amm2_ok hl hB hs h.ar (by omega) (by omega) (by omega) (by omega) h.y h.y)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hl hf (.inl (by omega)) (by omega),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, hf, hg, hrd, hwr, hx⟩
  exact VG.Proof.Bignum.mont_sq (hR p hp) (h.yv hq p hp) (hv p hp).2

/-- `Y := Y S / R`: `x^E R` and `S ≡ x^v R` give `x^(E+v) R`. -/
theorem mulS_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E v : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p))
    (h : ExpSt l s.mem B M k x Q E) (gs : ∀ p < 2, Good l s.mem B M l.oS p)
    (vs : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oS) % M p = x p ^ v p * 2 ^ (52 * l.L) % M p) :
    WP isa (amm l l.oY l.oY l.oS) s fun s' => ExpSt l s'.mem B M k x Q (fun p => E p + v p) ∧
      Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.mono (amm2_ok hl hB hs h.ar (by omega) (by omega) (by omega) (by omega) h.y gs)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hl hf (.inl (by omega)) (by omega),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, hf, hg, hrd, hwr, hx⟩
  exact mont_mul2 (hR p hp) (h.yv hq p hp) (vs hq p hp) (hv p hp).2

/-- After `4 - n` squarings, from `s₀`. -/
structure SqInv (l : Lay) (s₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (E : Nat → Nat) (n : Nat)
    (t : State) : Prop where
  r15 : t.gpr .r15 = BitVec.ofNat 64 n
  st : ExpSt l t.mem B M k x Q (fun p => E p * 2 ^ (4 - n))
  frame : Out2 l B l.oY l.NB s₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r15 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- The four squarings: `Y ≡ x^E R` becomes `x^(16 E) R`. -/
theorem sqLoop_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p))
    (h : ExpSt l s.mem B M k x Q E) :
    WP isa (.seq (.block [.mov32 .r15 (.imm 4)])
      (.loop (.seq (amm l l.oY l.oY l.oY) (.block [.alu .sub .r15 (.imm 1)])) .ne)) s
      fun s' => SqInv l s B M k x Q E 0 s' := by
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s.setReg32 .r15 4, rfl, WP.block_nil ?_⟩
  have i₀ : SqInv l s B M k x Q E 4 (s.setReg32 .r15 4) :=
    ⟨by rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl, by
      show ExpSt l s.mem B M k x Q (fun p => E p * 2 ^ (4 - 4))
      simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one]; exact h, Out2.refl _ _ _ _,
      fun r _ _ _ _ _ _ _ _ _ h15 => by rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ h15], rfl, rfl, rfl⟩
  refine WP.loop (M := isa) (c := .ne) (Q := SqInv l s B M k x Q E 0)
    (fun n t => 1 ≤ n ∧ n ≤ 4 ∧ SqInv l s B M k x Q E n t) ?_ 4 _ ⟨by decide, by decide, i₀⟩
  intro n t ⟨h1, h4, hI⟩
  have hB' : t.gpr .rbx = B := by
    rw [hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hB
  refine WP.seq (WP.mono (sq_ok hl hB' (hs.congr hI.wr) hR hI.st) fun t₁ ⟨st₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have r15₁ : t₁.gpr .r15 = BitVec.ofNat 64 n := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI.r15
  refine WP.mono (r15Dec_ok h1 h4 r15₁) fun t₂ ⟨r15₂, z₂, k₂, me₂, x₂⟩ => ?_
  have hI' : SqInv l s B M k x Q E (n - 1) t₂ := ⟨r15₂, ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_,
    by rw [k₂.2.1, rd₁, hI.rd], by rw [k₂.2.2, wr₁, hI.wr], by rw [x₂, x₁, hI.mxcsr]⟩
  · simp only [eval, z₂, Option.map_some]
    rcases Nat.eq_or_lt_of_le h1 with rfl | hn
    · exact .inl ⟨by simp, hI'⟩
    · exact .inr ⟨by simp only [decide_eq_false (show ¬ (n - 1 = 0) by omega), Bool.not_false], n - 1,
        by omega, by omega, by omega, hI'⟩
  · rw [me₂]
    refine ⟨st₁.ar, st₁.tab, st₁.y, fun hq p hp => ?_⟩
    rw [st₁.yv hq p hp, show 2 * (E p * 2 ^ (4 - n)) = E p * 2 ^ (4 - (n - 1)) by
      rw [show 4 - (n - 1) = (4 - n) + 1 by omega, Nat.pow_succ]; grind]
  · rw [me₂]; exact hI.frame.trans f₁
  · rw [k₂.gpr (by simp [r10]), g₁ r r1 r2 r3 r4 r5 r6 r7 r8 r9]
    exact hI.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10

theorem eaG' (t : State) (r : Reg) (d : Nat) : t.ea (at_ r d) = t.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  exact congrArg _ (BitVec.ofInt_natCast ..)

/-- `V` of prime `p` rotated up by 4 bits. -/
theorem rotV_ok {s : State} {B : Addr} {p : Nat} (hp : p < 2) (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * l.D)) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (l.D * p + l.oV))), .shift .ror .rax 60,
        .store (at_ .rbx (l.D * p + l.oV)) .rax]) s fun s' =>
      s'.mem = s.mem.writeW (off B (l.D * p + l.oV)) ((word s.mem B (l.D * p + l.oV)).rotateRight 60) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega
  have hd : l.D * p + l.oV + 8 ≤ 2 * l.D := by omega
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (l.D * p + l.oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region hd (by decide); ⟨_, List.mem_append_right _ h, c⟩
  have hst : InRegions s.wr (B + BitVec.ofNat 64 (l.D * p + l.oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region hd (by decide); ⟨_, h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' =>
    s'.mem = s.mem.writeW (off B (l.D * p + l.oV)) ((word s.mem B (l.D * p + l.oV)).rotateRight 60) ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [eaG', hB, hld, hst]
    and_intros <;> rfl) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

theorem Outside.limbG (hl : LayOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m') {c : Nat}
    (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hc' : c + l.NB ≤ 2 ^ 64) {j : Nat} (hj : j < l.L) :
    limb l m' B c j = limb l m B c j := by
  have := off_lt hl hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [h.word (by omega) (by omega)]

/-- `S := T_v` for both primes. -/
theorem sel2_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (h : ExpSt l s.mem B M k x Q E) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (select l 0 ++ select l 1))
      s fun s' => ExpSt l s'.mem B M k x Q E ∧
        (∀ p < 2, Good l s'.mem B M l.oS p ∧
          (Q → val52 l s'.mem B (l.D * p + l.oS) % M p = x p ^ nib l s.mem B p * 2 ^ (52 * l.L) % M p)) ∧
        (∀ p < 2, word s'.mem B (l.D * p + l.oV) = word s.mem B (l.D * p + l.oV)) ∧
        Out2 l B l.oS l.NB s.mem s'.mem ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hn := hs.nowrap
  refine wp_seqs_app (by simp [select]) (by simp [select])
    (WP.mono (select_ok hl (p := 0) (by decide) hB hs) fun s₁ ⟨l₁, o₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have hB₁ : s₁.gpr .rbx = B := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hB
  refine WP.mono (select_ok hl (p := 1) (by decide) hB₁ (hs.congr wr₁)) fun s₂ ⟨l₂, o₂, g₂, rd₂, wr₂, x₂⟩ => ?_
  have f₁ : Out2 l B l.oS l.NB s.mem s₁.mem := Out2.of_outside (p := 0) (by decide) o₁
  have f₂ : Out2 l B l.oS l.NB s₁.mem s₂.mem := Out2.of_outside (p := 1) (by decide) o₂
  have v₁ : nib l s₁.mem B 1 = nib l s.mem B 1 := by
    unfold nib; rw [o₁.word (by omega) (by omega)]
  have ex₁ := h.tab_of hl f₁ (.inl (by omega)) (by omega)
  -- entry 0 and entry 1
  have hv0 := nib_lt (l := l) s.mem B 0
  have hv1 := nib_lt (l := l) s.mem B 1
  have t0 := h.tab (nib l s.mem B 0) hv0 0 (by decide)
  have t1 := ex₁ (nib l s.mem B 1) hv1 1 (by decide)
  have hN0 : l.NB * nib l s.mem B 0 + l.NB ≤ 16 * l.NB := by
    rw [← Nat.mul_succ, Nat.mul_comm 16]; exact Nat.mul_le_mul_left _ hv0
  have L0 : ∀ q < l.L, limb l s₂.mem B (l.D * 0 + l.oS) q =
      limb l s.mem B (l.D * 0 + (l.oTab + l.NB * nib l s.mem B 0)) q := fun q hq => by
    rw [Outside.limbG hl o₂ (.inl (by omega)) (by omega) hq, l₁ q hq, Nat.add_assoc]
  have L1 : ∀ q < l.L, limb l s₂.mem B (l.D * 1 + l.oS) q =
      limb l s₁.mem B (l.D * 1 + (l.oTab + l.NB * nib l s.mem B 1)) q :=
    fun q hq => by rw [l₂ q hq, v₁, Nat.add_assoc]
  refine ⟨⟨?_, h.tab_of hl (f₁.trans f₂) (.inl (by omega)) (by omega), fun p hp => ?_, fun hq p hp => ?_⟩,
    fun p hp => ?_, fun p hp => ?_, f₁.trans f₂, fun r r1 r2 r3 r4 => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    by rw [x₂, x₁]⟩
  · exact (h.ar.of_out2 hl f₁ (by omega) (by omega)).of_out2 hl f₂ (by omega) (by omega)
  · exact (h.y p hp).of_out2 hl hp (f₁.trans f₂) (.inl (by omega)) (by omega) (by omega)
  · rw [(f₁.trans f₂).val hl hp (.inl (by omega)) (by omega) (by omega)]; exact h.yv hq p hp
  · rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
    · exact ⟨t0.1.of_limbs L0, fun hq => by rw [val52_of_limbs L0]; exact t0.2 hq⟩
    · exact ⟨t1.1.of_limbs L1, fun hq => by rw [val52_of_limbs L1]; exact t1.2 hq⟩
  · rw [(f₁.trans f₂).word_at hl hp (.inr (by omega)) (by omega) (by omega)]
  · rw [g₂ r r1 r2 r3 r4, g₁ r r1 r2 r3 r4]

/-- The rotations of both primes' `V`. -/
def rotCode (l : Lay) (p : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rbx (l.D * p + l.oV))), .shift .ror .rax 60, .store (at_ .rbx (l.D * p + l.oV)) .rax]

theorem window_eq : window l =
    ([.block [.mov32 .r15 (.imm 4)],
      .loop (.seq (amm l l.oY l.oY l.oY) (.block [.alu .sub .r15 (.imm 1)])) .ne] : List (Prog isa)) ++
    ((select l 0 ++ select l 1) ++
      ([.block (rotCode l 0 ++ rotCode l 1), amm l l.oY l.oY l.oS] : List (Prog isa))) := by
  simp only [window, List.append_assoc]; rfl

/-- A window: `Y ≡ x^E R` becomes `x^(16 E + v) R` for the top 4 bits `v` of
`V`, which is rotated up by 4 bits. -/
theorem window_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p))
    (h : ExpSt l s.mem B M k x Q E) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (window l)) s fun s' =>
      ExpSt l s'.mem B M k x Q (fun p => E p * 16 + nib l s.mem B p) ∧
      (∀ p < 2, word s'.mem B (l.D * p + l.oV) = (word s.mem B (l.D * p + l.oV)).rotateRight 60) ∧
      OutW l B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hn := hs.nowrap
  rw [window_eq]
  refine wp_seqs_app (by simp) (by simp) (WP.mono (sqLoop_ok hl hB hs hR h) fun s₁ i₁ => ?_)
  have hB₁ : s₁.gpr .rbx = B := by
    rw [i₁.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hB
  have w₁ : ∀ p < 2, word s₁.mem B (l.D * p + l.oV) = word s.mem B (l.D * p + l.oV) := fun p hp =>
    i₁.frame.word_at hl hp (.inr (by omega)) (by omega) (by omega)
  have nib₁ : ∀ p < 2, nib l s₁.mem B p = nib l s.mem B p := fun p hp => by unfold nib; rw [w₁ p hp]
  refine wp_seqs_app (by simp [select]) (by simp)
    (WP.mono (sel2_ok hl hB₁ (hs.congr i₁.wr) i₁.st) fun s₂ ⟨st₂, gs₂, w₂, f₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have hB₂ : s₂.gpr .rbx = B := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hB₁
  have hs₂ : Scr s₂ B (2 * l.D) := hs.congr (by rw [wr₂, i₁.wr])
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rotV_ok (p := 0) (by decide) hB₂ hs₂) fun s₃ ⟨m₃, k₃, x₃⟩ => ?_
  have hB₃ : s₃.gpr .rbx = B := by rw [k₃.gpr (by decide)]; exact hB₂
  refine WP.mono (rotV_ok (p := 1) (by decide) hB₃ (hs₂.congr k₃.2.2)) fun s₄ ⟨m₄, k₄, x₄⟩ => ?_
  have o₃ : Outside B (l.D * 0 + l.oV) 8 s₂.mem s₃.mem := by
    rw [m₃]; exact writeW_outside _ B _ (by omega)
  have o₄ : Outside B (l.D * 1 + l.oV) 8 s₃.mem s₄.mem := by
    rw [m₄]; exact writeW_outside _ B _ (by omega)
  have f₄ : Out2 l B l.oV 8 s₂.mem s₄.mem :=
    (Out2.of_outside (p := 0) (by decide) o₃).trans (Out2.of_outside (p := 1) (by decide) o₄)
  have hB₄ : s₄.gpr .rbx = B := by rw [k₄.gpr (by decide)]; exact hB₃
  have st₄ : ExpSt l s₄.mem B M k x Q (fun p => E p * 2 ^ (4 - 0)) :=
    ⟨st₂.ar.of_out2 hl f₄ (by omega) (by omega), st₂.tab_of hl f₄ (.inr (by omega)) (by omega),
      fun p hp => (st₂.y p hp).of_out2 hl hp f₄ (.inl (by omega)) (by omega) (by omega),
      fun hq p hp => by rw [f₄.val hl hp (.inl (by omega)) (by omega) (by omega)]; exact st₂.yv hq p hp⟩
  refine WP.mono (mulS_ok hl (v := fun p => nib l s₁.mem B p) hB₄ (hs₂.congr (by rw [k₄.2.2, k₃.2.2])) hR st₄
    (fun p hp => ((gs₂ p hp).1).of_out2 hl hp f₄ (.inl (by omega)) (by omega) (by omega))
    (fun hq p hp => by rw [f₄.val hl hp (.inl (by omega)) (by omega) (by omega)]; exact (gs₂ p hp).2 hq))
    fun s₅ ⟨st₅, f₅, g₅, rd₅, wr₅, x₅⟩ => ⟨?_, fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_,
      by rw [rd₅, k₄.2.1, k₃.2.1, rd₂, i₁.rd], by rw [wr₅, k₄.2.2, k₃.2.2, wr₂, i₁.wr],
      by rw [x₅, x₄, x₃, x₂, i₁.mxcsr]⟩
  · refine ⟨st₅.ar, st₅.tab, st₅.y, fun hq p hp => ?_⟩
    rw [st₅.yv hq p hp, nib₁ p hp]
  · rw [f₅.word_at hl hp (.inr (by omega)) (by omega) (by omega)]
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
    · rw [o₄.word (by omega) (by omega), m₃, VG.Proof.Bignum.word_writeW_self,
        w₂ 0 (by decide), w₁ 0 (by decide)]
    · rw [m₄, VG.Proof.Bignum.word_writeW_self, o₃.word (by omega) (by omega),
        w₂ 1 (by decide), w₁ 1 (by decide)]
  · exact ((OutW.ofY i₁.frame).trans (OutW.ofS f₂)).trans ((OutW.ofV f₄).trans (OutW.ofY f₅))
  · rw [g₅ r r1 r2 r3 r4 r5 r6 r7 r8 r9, k₄.gpr (by simp [r1]), k₃.gpr (by simp [r1]), g₂ r r1 r2 r3 r5]
    exact i₁.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10

end VG.Proof.Bignum.X86_64.G
