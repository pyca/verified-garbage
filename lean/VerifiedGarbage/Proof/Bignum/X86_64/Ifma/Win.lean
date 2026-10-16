module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Tab
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with AVX512_IFMA on x86-64, any size: a window of the exponentiations

`ExpSt`: the regions' moduli (`Ar`), the table
(`T_j ≡ x^j R`) and `Y ≡ x^E R` for each prime, `R = 2^(208 R)`. A window
(`window_ok`) squares `Y` four times (`sq_ok`), reads `T_v` into `S` for
the top 4 bits `v` of each prime's quadword at `oV` (`select_ok`), rotates
that quadword up by 4 bits, and multiplies `Y` by `S` (`mulS_ok`):
`Y ≡ x^(16 E + v) R`. It writes only `Y`, `S` and `V` of each region
(`OutW`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (mont_mul2 r15Dec_ok ea_at' wp_seqs_app se_ofNat)
open VG.Proof.Bignum.X86_64 (ofNat_sub_beq)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The state of the exponentiations: `Y ≡ x^E R`. -/
structure ExpSt (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (E : Nat → Nat) : Prop where
  ar : Ar l m B M k
  tab : ∀ j < 16, ∀ p < 2, Good l m B M (l.oTab + l.NB * j) p ∧
    (Q → val52 l m B (l.D * p + (l.oTab + l.NB * j)) % M p = x p ^ j * 2 ^ (52 * l.S) % M p)
  y : ∀ p < 2, Good l m B M l.oY p
  yv : Q → ∀ p < 2, val52 l m B (l.D * p + l.oY) % M p = x p ^ E p * 2 ^ (52 * l.S) % M p

/-- `m'` agrees with `m` but on `Y`, `S` and `V` of each region. -/
def OutW (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (m m' : Mem) : Prop :=
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
      (Q → val52 l m' B (l.D * p + (l.oTab + l.NB * j)) % M p = x p ^ j * 2 ^ (52 * l.S) % M p) :=
  fun j hj p hp => by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hNj : l.NB * j + l.NB ≤ 16 * l.NB := by
    rw [← Nat.mul_succ, Nat.mul_comm 16]; exact Nat.mul_le_mul_left _ hj
  have hc : l.oTab + l.NB * j + l.NB ≤ o ∨ o + n ≤ l.oTab + l.NB * j := by
    rcases ho with ho | ho
    · exact .inr (by omega_using [ho])
    · exact .inl (by omega_using [hNj, ho])
  have hcD : l.oTab + l.NB * j + l.NB ≤ l.D := by omega_using [o5, o10, hNj]
  obtain ⟨g, v⟩ := h.tab j hj p hp
  exact ⟨g.of_out2 hl hp hf hc hcD hoD, fun hq => by rw [hf.val hl hp hc hcD hoD]; exact v hq⟩

/-- `Y := Y² / R`: `x^E R` becomes `x^(2E) R`. -/
theorem sq_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) :
    WP isa (amm l l.oY l.oY l.oY) s fun s' => ExpSt l s'.mem B M k x Q (fun p => 2 * E p) ∧
      Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.mono (amm2_ok hl hB hs h.ar (by omega_using [o2, o10]) (by omega_using []) (by omega_using [o2, o10])
      (by omega_using [o2, o10]) h.y h.y)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hl hf (.inl (by omega_using [o2, o5])) (by omega_using [o2, o10]),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, hf, hg, hrd, hwr, hx⟩
  exact VG.Proof.Bignum.mont_sq (hR p hp) (h.yv hq p hp) (hv p hp).2

/-- `Y := Y S / R`: `x^E R` and `S ≡ x^v R` give `x^(E+v) R`. -/
theorem mulS_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E v : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) (gs : ∀ p < 2, Good l s.mem B M l.oS p)
    (vs : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oS) % M p = x p ^ v p * 2 ^ (52 * l.S) % M p) :
    WP isa (amm l l.oY l.oY l.oS) s fun s' => ExpSt l s'.mem B M k x Q (fun p => E p + v p) ∧
      Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.mono (amm2_ok hl hB hs h.ar (by omega_using [o2, o10]) (by omega_using []) (by omega_using [o2, o10])
      (by omega_using [o4, o10]) h.y gs)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hl hf (.inl (by omega_using [o2, o5])) (by omega_using [o2, o10]),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, hf, hg, hrd, hwr, hx⟩
  exact mont_mul2 (hR p hp) (h.yv hq p hp) (vs hq p hp) (hv p hp).2

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
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  have hd : l.D * p + l.oV + 8 ≤ 2 * l.D := by omega_using [o8, o10, hDp]
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
  rw [h.word (by omega_using [hc, this]) (by omega_using [hc', this])]

/-- `S := T_v` for both primes. -/
theorem sel2_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (h : ExpSt l s.mem B M k x Q E) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (select l 0 ++ select l 1))
      s fun s' => ExpSt l s'.mem B M k x Q E ∧
        (∀ p < 2, Good l s'.mem B M l.oS p ∧
          (Q → val52 l s'.mem B (l.D * p + l.oS) % M p = x p ^ nib l s.mem B p * 2 ^ (52 * l.S) % M p)) ∧
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
    unfold nib; rw [o₁.word (by omega_using [o4, o10]) (by omega_using [o8, o10, hn])]
  have ex₁ := h.tab_of hl f₁ (.inl (by omega_using [o4, o5])) (by omega_using [o4, o10])
  -- entry 0 and entry 1
  have hv0 := nib_lt (l := l) s.mem B 0
  have hv1 := nib_lt (l := l) s.mem B 1
  have t0 := h.tab (nib l s.mem B 0) hv0 0 (by decide)
  have t1 := ex₁ (nib l s.mem B 1) hv1 1 (by decide)
  have hN0 : l.NB * nib l s.mem B 0 + l.NB ≤ 16 * l.NB := by
    rw [← Nat.mul_succ, Nat.mul_comm 16]; exact Nat.mul_le_mul_left _ hv0
  have L0 : ∀ q < l.L, limb l s₂.mem B (l.D * 0 + l.oS) q =
      limb l s.mem B (l.D * 0 + (l.oTab + l.NB * nib l s.mem B 0)) q := fun q hq => by
    rw [Outside.limbG hl o₂ (.inl (by omega_using [hD])) (by omega_using [o4, hD]) hq, l₁ q hq, Nat.add_assoc]
  have L1 : ∀ q < l.L, limb l s₂.mem B (l.D * 1 + l.oS) q =
      limb l s₁.mem B (l.D * 1 + (l.oTab + l.NB * nib l s.mem B 1)) q :=
    fun q hq => by rw [l₂ q hq, v₁, Nat.add_assoc]
  refine ⟨⟨?_, h.tab_of hl (f₁.trans f₂) (.inl (by omega_using [o4, o5])) (by omega_using [o4, o10]), fun p hp => ?_, fun hq p hp => ?_⟩,
    fun p hp => ?_, fun p hp => ?_, f₁.trans f₂, fun r r1 r2 r3 r4 => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    by rw [x₂, x₁]⟩
  · exact (h.ar.of_out2 hl f₁ (by omega_using [o2, o4]) (by omega_using [o4, o10])).of_out2 hl f₂
      (by omega_using [o2, o4]) (by omega_using [o4, o10])
  · exact (h.y p hp).of_out2 hl hp (f₁.trans f₂) (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])
  · rw [(f₁.trans f₂).val hl hp (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])]; exact h.yv hq p hp
  · rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl
    · exact ⟨t0.1.of_limbs L0, fun hq => by rw [val52_of_limbs L0]; exact t0.2 hq⟩
    · exact ⟨t1.1.of_limbs L1, fun hq => by rw [val52_of_limbs L1]; exact t1.2 hq⟩
  · rw [(f₁.trans f₂).word_at hl hp (.inr (by omega_using [o4, o8])) (by omega_using [o8, o10]) (by omega_using [o4, o10])]
  · rw [g₂ r r1 r2 r3 r4, g₁ r r1 r2 r3 r4]

/-- The rotations of both primes' `V`. -/
def rotCode (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rbx (l.D * p + l.oV))), .shift .ror .rax 60, .store (at_ .rbx (l.D * p + l.oV)) .rax]

theorem amm_winSetup (b : Nat) : amm l l.oY l.oY b = .seq (.block (winSetup l b)) (ammCore l) := rfl

/-- The comparison of `r15` with 1. -/
theorem r15Cmp_ok {s : State} {n : Nat} (hn : n ≤ 5) (h15 : s.gpr .r15 = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .cmp .r15 (.imm 1)]) s fun s' =>
      isa.eval .e s' = some (n == 1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  let t := arithFlags s (s.gpr .r15 - (1 : BitVec 32).signExtend 64)
    (decide ((s.gpr .r15).toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow (s.gpr .r15) ((1 : BitVec 32).signExtend 64) (s.gpr .r15 - (1 : BitVec 32).signExtend 64))
  refine WP.of_runBlock ⟨t, by rw [runBlock_cons]; rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change t.zf = _
    simp only [t, VG.X86_64.RegUpd.zf_arithFlags, h15]
    rcases n with _ | _ | _ | _ | _ | _ | n <;> first | omega | decide
  all_goals rfl

/-- The loop of a window with `n` multiplications left, from `s₀`. -/
structure MulInv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (M k x : Nat → Nat)
    (Q : Prop) (E v : Nat → Nat) (n : Nat) (t : State) : Prop where
  r15 : t.gpr .r15 = BitVec.ofNat 64 n
  st : ExpSt l t.mem B M k x Q (fun p => E p * 2 ^ (5 - n))
  gs : ∀ p < 2, Good l t.mem B M l.oS p ∧
    (Q → val52 l t.mem B (l.D * p + l.oS) % M p = x p ^ v p * 2 ^ (52 * l.S) % M p)
  frame : Out2 l B l.oY l.NB s₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r15 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- The loop body of a window. -/
def mulBody (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prog isa :=
  .seq (.block [.alu .cmp .r15 (.imm 1)])
    (.seq (.ite .e (.block (winSetup l l.oS)) (.block (winSetup l l.oY)))
      (.seq (ammCore l) (.block [.alu .sub .r15 (.imm 1)])))

/-- The five multiplications: four squarings, then `Y S`. `Y ≡ x^E R` and
`S ≡ x^v R` give `Y ≡ x^(16 E + v) R`. -/
theorem mulLoop_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E v : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : MulInv l s B M k x Q E v 5 s) :
    WP isa (.loop (mulBody l) .ne) s fun s' =>
      ExpSt l s'.mem B M k x Q (fun p => E p * 16 + v p) ∧ Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ 5 ∧ MulInv l s B M k x Q E v n t) ?_ 5 s
    ⟨by decide, by decide, h⟩
  intro n t ⟨h1, h5, hI⟩
  have hB' : t.gpr .rbx = B := by
    rw [hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hB
  refine WP.seq (WP.mono (r15Cmp_ok h5 hI.r15) fun t₀ ⟨e₀, g₀, m₀, rd₀, wr₀, x₀⟩ => ?_)
  have hB₀ : t₀.gpr .rbx = B := by rw [g₀]; exact hB'
  have hs₀ : Scr t₀ B (2 * l.D) := hs.congr (by rw [wr₀, hI.wr])
  have st₀ : ExpSt l t₀.mem B M k x Q (fun p => E p * 2 ^ (5 - n)) := by rw [m₀]; exact hI.st
  -- after the multiplication and the count
  have after : ∀ (t₁ : State) (E' : Nat → Nat), ExpSt l t₁.mem B M k x Q E' →
      Out2 l B l.oY l.NB t₀.mem t₁.mem →
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .r12 → t₁.gpr r = t₀.gpr r) → t₁.rd = t₀.rd → t₁.wr = t₀.wr → t₁.mxcsr = t₀.mxcsr →
      (n = 1 → E' = fun p => E p * 16 + v p) → (1 < n → E' = fun p => E p * 2 ^ (5 - (n - 1))) →
      WP isa (.block [.alu .sub .r15 (.imm 1)]) t₁ fun t₂ =>
        (isa.eval .ne t₂ = some false ∧ (ExpSt l t₂.mem B M k x Q (fun p => E p * 16 + v p) ∧
          Out2 l B l.oY l.NB s.mem t₂.mem ∧
          (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
            r ≠ .r12 → r ≠ .r15 → t₂.gpr r = s.gpr r) ∧
          t₂.rd = s.rd ∧ t₂.wr = s.wr ∧ t₂.mxcsr = s.mxcsr)) ∨
        (isa.eval .ne t₂ = some true ∧ ∃ m < n, 1 ≤ m ∧ m ≤ 5 ∧ MulInv l s B M k x Q E v m t₂) := by
    intro t₁ E' st₁ f₁ g₁ rd₁ wr₁ x₁ hlast hmore
    have r15₁ : t₁.gpr .r15 = BitVec.ofNat 64 n := by
      rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), g₀]; exact hI.r15
    refine WP.mono (r15Dec_ok h1 h5 r15₁) fun t₂ ⟨r15₂, z₂, k₂, me₂, x₂⟩ => ?_
    have f₀₁ : Out2 l B l.oY l.NB t.mem t₁.mem := by rw [← m₀]; exact f₁
    have f₂ : Out2 l B l.oY l.NB s.mem t₂.mem := by rw [me₂]; exact hI.frame.trans f₀₁
    have g₂ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .r12 → r ≠ .r15 → t₂.gpr r = s.gpr r := fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => by
      rw [k₂.gpr (by simp [r10]), g₁ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₀]
      exact hI.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
    have rd₂ : t₂.rd = s.rd := by rw [k₂.2.1, rd₁, rd₀, hI.rd]
    have wr₂ : t₂.wr = s.wr := by rw [k₂.2.2, wr₁, wr₀, hI.wr]
    have xx₂ : t₂.mxcsr = s.mxcsr := by rw [x₂, x₁, x₀, hI.mxcsr]
    simp only [eval, z₂, Option.map_some]
    rcases Nat.eq_or_lt_of_le h1 with rfl | hn
    · refine .inl ⟨by simp, ?_, f₂, g₂, rd₂, wr₂, xx₂⟩
      rw [me₂, ← hlast rfl]; exact st₁
    · refine .inr ⟨by simp only [decide_eq_false (show ¬ (n - 1 = 0) by omega_using [hn]),
        Bool.not_false], n - 1, by omega_using [hn], by omega_using [hn], by omega_using [h5],
        r15₂, ?_, ?_, f₂, g₂, rd₂, wr₂, xx₂⟩
      · rw [me₂, ← hmore hn]; exact st₁
      · intro p hp
        have hf : Out2 l B l.oY l.NB t.mem t₂.mem := by rw [me₂]; exact f₀₁
        obtain ⟨g, w⟩ := hI.gs p hp
        exact ⟨g.of_out2 hl hp hf (.inr (by omega_using [o2, o4])) (by omega_using [o4, o10]) (by omega_using [o2, o10]),
          fun hq => by rw [hf.val hl hp (.inr (by omega_using [o2, o4])) (by omega_using [o4, o10]) (by omega_using [o2, o10])]; exact w hq⟩
  refine WP.seq ?_
  by_cases h1' : n = 1
  · subst n
    refine WP.ite true e₀ (fun _ => ?_) (fun h => Bool.noConfusion h)
    have hm := mulS_ok hl (v := v) hB₀ hs₀ hR st₀
      (fun p hp => by rw [m₀]; exact (hI.gs p hp).1) (fun hq p hp => by rw [m₀]; exact (hI.gs p hp).2 hq)
    rw [amm_winSetup, WP.seq_iff] at hm
    refine WP.mono hm fun u hu => WP.seq (WP.mono hu fun t₁ ⟨st₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
    refine after t₁ _ st₁ f₁ g₁ rd₁ wr₁ x₁ (fun _ => ?_) (fun h => absurd h (by decide))
    funext p; rfl
  · refine WP.ite false (by rw [e₀]; simp [h1']) (fun h => Bool.noConfusion h) (fun _ => ?_)
    have hm := sq_ok hl hB₀ hs₀ hR st₀
    rw [amm_winSetup, WP.seq_iff] at hm
    refine WP.mono hm fun u hu => WP.seq (WP.mono hu fun t₁ ⟨st₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
    refine after t₁ _ st₁ f₁ g₁ rd₁ wr₁ x₁ (fun h => absurd h h1') (fun _ => ?_)
    funext p
    rw [show 5 - (n - 1) = (5 - n) + 1 by omega_using [h1, h5, h1'], Nat.pow_succ]; grind

/-- The last window's setup: `S := Fin`, one multiplication, the last window. -/
def finCode (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  copyN l l.oS l.oFin ++ [.mov32 .r15 (.imm 1), .mov32 .r14 (.imm 1)]

/-- A window's usual setup: `S := T_v`, `V` rotated, five multiplications. -/
def normCode (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List (Prog isa) :=
  (select l 0 ++ select l 1) ++
    ([.block (rotCode l 0 ++ rotCode l 1 ++ ([.mov32 .r15 (.imm 5)] : List Instr))] : List (Prog isa))

theorem window_eq : VG.Impl.Bignum.X86_64.seqs (window l) =
    .seq (.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 l.E))])
      (.ite .e (.block (finCode l)) (VG.Impl.Bignum.X86_64.seqs (normCode l)))) (.loop (mulBody l) .ne) := by
  simp only [window, normCode, finCode, List.append_assoc]; rfl

theorem E_lt (hl : LayOk l) : l.E < 2 ^ 31 := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have := hl.D_bounds; omega_arith

/-- The comparison of `r13` (byte `i`) with `E`. -/
theorem r13Cmp_ok (hl : LayOk l) {s : State} {i : Nat} (hi : i ≤ l.E) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 l.E))]) s fun s' =>
      isa.eval .e s' = some (decide (i = l.E)) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hE := E_lt hl
  let t := arithFlags s (s.gpr .r13 - (BitVec.ofNat 32 l.E).signExtend 64)
    (decide ((s.gpr .r13).toNat < ((BitVec.ofNat 32 l.E).signExtend 64).toNat))
    (subOverflow (s.gpr .r13) ((BitVec.ofNat 32 l.E).signExtend 64) (s.gpr .r13 - (BitVec.ofNat 32 l.E).signExtend 64))
  refine WP.of_runBlock ⟨t, by rw [runBlock_cons]; rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change t.zf = _
    simp only [t, VG.X86_64.RegUpd.zf_arithFlags, h13, se_ofNat hE]
    rw [ofNat_sub_beq (by omega_using [hi, hE]) (by omega_using [hE])]
  all_goals rfl

/-- A window's usual setup and multiplications: `Y ≡ x^E R` becomes
`x^(16 E + v) R` for the top 4 bits `v` of `V`, which is rotated up by 4 bits. -/
theorem winNorm_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (normCode l)) s fun t => WP isa (.loop (mulBody l) .ne) t fun s' =>
      ExpSt l s'.mem B M k x Q (fun p => E p * 16 + nib l s.mem B p) ∧
      (∀ p < 2, word s'.mem B (l.D * p + l.oV) = (word s.mem B (l.D * p + l.oV)).rotateRight 60) ∧
      OutW l B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hn := hs.nowrap
  refine wp_seqs_app (by simp [select]) (by simp)
    (WP.mono (sel2_ok hl hB hs h) fun s₂ ⟨st₂, gs₂, w₂, f₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have hB₂ : s₂.gpr .rbx = B := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hB
  have hs₂ : Scr s₂ B (2 * l.D) := hs.congr wr₂
  dsimp only [VG.Impl.Bignum.X86_64.seqs]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (rotV_ok (p := 0) (by decide) hB₂ hs₂) fun s₃ ⟨m₃, k₃, x₃⟩ => ?_
  have hB₃ : s₃.gpr .rbx = B := by rw [k₃.gpr (by decide)]; exact hB₂
  refine WP.mono (rotV_ok (p := 1) (by decide) hB₃ (hs₂.congr k₃.2.2)) fun s₄ ⟨m₄, k₄, x₄⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨s₄.setReg32 .r15 5, rfl, WP.block_nil ?_⟩
  have o₃ : Outside B (l.D * 0 + l.oV) 8 s₂.mem s₃.mem := by
    rw [m₃]; exact writeW_outside _ B _ (by omega_using [o8, o10, hn])
  have o₄ : Outside B (l.D * 1 + l.oV) 8 s₃.mem s₄.mem := by
    rw [m₄]; exact writeW_outside _ B _ (by omega_using [o8, o10, hn])
  have f₄ : Out2 l B l.oV 8 s₂.mem s₄.mem :=
    (Out2.of_outside (p := 0) (by decide) o₃).trans (Out2.of_outside (p := 1) (by decide) o₄)
  have hB₄ : s₄.gpr .rbx = B := by rw [k₄.gpr (by decide)]; exact hB₃
  let s₅ := s₄.setReg32 .r15 5
  have hB₅ : s₅.gpr .rbx = B := by
    change (s₄.setReg32 .r15 5).gpr .rbx = _
    rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB₄
  have st₄ : ExpSt l s₅.mem B M k x Q (fun p => E p * 2 ^ (5 - 5)) :=
    ⟨st₂.ar.of_out2 hl f₄ (by omega_using [o2, o8]) (by omega_using [o8, o10]),
        st₂.tab_of hl f₄ (.inr (by omega_using [o5, o8])) (by omega_using [o8, o10]),
      fun p hp => (st₂.y p hp).of_out2 hl hp f₄ (.inl (by omega_using [o2, o8])) (by omega_using [o2, o10]) (by omega_using [o8, o10]),
      fun hq p hp => by
        rw [show E p * 2 ^ (5 - 5) = E p by simp]
        change val52 l s₄.mem B _ % M p = _
        rw [f₄.val hl hp (.inl (by omega_using [o2, o8])) (by omega_using [o2, o10]) (by omega_using [o8, o10])]
        exact st₂.yv hq p hp⟩
  have hI : MulInv l s₅ B M k x Q E (fun p => nib l s.mem B p) 5 s₅ :=
    ⟨by change (s₄.setReg32 .r15 5).gpr .r15 = _; rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl, st₄,
      fun p hp => ⟨((gs₂ p hp).1).of_out2 hl hp f₄ (.inl (by omega_using [o4, o8])) (by omega_using [o4, o10])
        (by omega_using [o8, o10]), fun hq => by
        change val52 l s₄.mem B _ % M p = _
        rw [f₄.val hl hp (.inl (by omega_using [o4, o8])) (by omega_using [o4, o10]) (by omega_using [o8, o10])]
        exact (gs₂ p hp).2 hq⟩,
      Out2.refl _ _ _ _, fun _ _ _ _ _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.mono (mulLoop_ok hl hB₅ (hs₂.congr (by
      change s₄.wr = _; rw [k₄.2.2, k₃.2.2])) hR hI)
    fun s₆ ⟨st₆, f₆, g₆, rd₆, wr₆, x₆⟩ => ⟨st₆, fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_,
      by rw [rd₆]; change s₄.rd = _; rw [k₄.2.1, k₃.2.1, rd₂],
      by rw [wr₆]; change s₄.wr = _; rw [k₄.2.2, k₃.2.2, wr₂],
      by rw [x₆]; change s₄.mxcsr = _; rw [x₄, x₃, x₂]⟩
  · rw [f₆.word_at hl hp (.inr (by omega_using [o2, o8])) (by omega_using [o8, o10]) (by omega_using [o2, o10])]
    change word s₄.mem B _ = _
    rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl
    · rw [o₄.word (by omega_using [o10]) (by omega_using [o8, o10, hn]), m₃, VG.Proof.Bignum.word_writeW_self,
        w₂ 0 (by decide)]
    · rw [m₄, VG.Proof.Bignum.word_writeW_self, o₃.word (by omega_using [o10]) (by omega_arith),
        w₂ 1 (by decide)]
  · exact ((OutW.ofS f₂).trans (OutW.ofV f₄)).trans (OutW.ofY f₆)
  · rw [g₆ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10]
    change (s₄.setReg32 .r15 5).gpr r = _
    rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ r10, k₄.gpr (by simp [r1]), k₃.gpr (by simp [r1]),
      g₂ r r1 r2 r3 r5]

/-- A window (byte `i < E`): `Y ≡ x^E R` becomes `x^(16 E + v) R` for the top
4 bits `v` of `V`, which is rotated up by 4 bits. -/
theorem window_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat} {i : Nat}
    (hi : i < l.E) (h13 : s.gpr .r13 = BitVec.ofNat 64 i)
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (window l)) s fun s' =>
      ExpSt l s'.mem B M k x Q (fun p => E p * 16 + nib l s.mem B p) ∧
      (∀ p < 2, word s'.mem B (l.D * p + l.oV) = (word s.mem B (l.D * p + l.oV)).rotateRight 60) ∧
      OutW l B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  rw [window_eq]
  refine WP.seq (WP.seq (WP.mono (r13Cmp_ok hl (Nat.le_of_lt hi) h13) fun s₀ ⟨e₀, g₀, m₀, rd₀, wr₀, x₀⟩ => ?_))
  refine WP.ite false (by rw [e₀]; simp only [decide_eq_false (Nat.ne_of_lt hi)]) (fun h => Bool.noConfusion h)
    (fun _ => ?_)
  have := winNorm_ok hl (s := s₀) (by rw [g₀]; exact hB) (hs.congr wr₀) hR (m₀ ▸ h)
  rw [m₀, g₀, rd₀, wr₀, x₀] at this
  exact this

/-- `S` holds `Fin`, `r14` and `r15` 1, from `s₀`. -/
structure FinSet (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (t : State) : Prop where
  s : ∀ p < 2, ∀ q < l.L, limb l t.mem B (l.D * p + l.oS) q = limb l s₀.mem B (l.D * p + l.oFin) q
  frame : Out2 l B l.oS l.NB s₀.mem t.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 1
  r15 : t.gpr .r15 = BitVec.ofNat 64 1
  gpr : ∀ r, r ≠ .r14 → r ≠ .r15 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

theorem finCode_ok (hl : LayOk l) {s : State} {B : Addr} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) :
    WP isa (.block (finCode l)) s (FinSet l s B) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  rw [finCode, WP.block_append_iff]
  refine WP.mono (copyN_ok hl hB hs (by omega_using [o4, o10]) (by omega_using [o9, o10])
    (.inr (by omega_using [o4, o9]))) fun s₁ ⟨l₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁.setReg32 .r15 1, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨(s₁.setReg32 .r15 1).setReg32 .r14 1, rfl, WP.block_nil ⟨l₁, f₁, ?_, ?_, fun r r1 r2 => ?_, rd₁, wr₁, x₁⟩⟩
  · rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl
  · rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ (by decide), State.setReg32, RegUpd.gpr_setReg_self]; rfl
  · rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ r1, State.setReg32, RegUpd.gpr_setReg_of_ne _ _ r2, g₁]

/-- The last window (`r13 = E`): `Y := Y Fin / R`, `r14 := 1`. -/
theorem finWin_ok (hl : LayOk l) {s : State} {B : Addr} {M k : Nat → Nat}
    (h13 : s.gpr .r13 = BitVec.ofNat 64 l.E) (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D))
    (ar : Ar l s.mem B M k) (gy : ∀ p < 2, Good l s.mem B M l.oY p) (gf : ∀ p < 2, Good l s.mem B M l.oFin p) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (window l)) s fun s' =>
      (∀ p < 2, Good l s'.mem B M l.oY p ∧
        val52 l s'.mem B (l.D * p + l.oY) * 2 ^ (52 * l.S) % M p =
          val52 l s.mem B (l.D * p + l.oY) * val52 l s.mem B (l.D * p + l.oFin) % M p) ∧
      OutW l B s.mem s'.mem ∧ s'.gpr .r14 = BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  rw [window_eq]
  refine WP.seq (WP.seq (WP.mono (r13Cmp_ok hl (Nat.le_refl _) h13) fun s₀ ⟨e₀, g₀, m₀, rd₀, wr₀, x₀⟩ => ?_))
  refine WP.ite true (by rw [e₀]; simp only [decide_true]) (fun _ => ?_) (fun h => Bool.noConfusion h)
  have hB₀ : s₀.gpr .rbx = B := by rw [g₀]; exact hB
  refine WP.mono (finCode_ok hl hB₀ (hs.congr wr₀)) fun u hu => ?_
  have hBu : u.gpr .rbx = B := by rw [hu.gpr _ (by decide) (by decide)]; exact hB₀
  have hsu : Scr u B (2 * l.D) := hs.congr (by rw [hu.wr, wr₀])
  have fu : Out2 l B l.oS l.NB s.mem u.mem := by rw [← m₀]; exact hu.frame
  have gsu : ∀ p < 2, Good l u.mem B M l.oS p := fun p hp =>
    (gf p hp).of_limbs fun q hq => by rw [hu.s p hp q hq, m₀]
  have vsu : ∀ p < 2, val52 l u.mem B (l.D * p + l.oS) = val52 l s.mem B (l.D * p + l.oFin) := fun p hp =>
    val52_of_limbs fun q hq => by rw [hu.s p hp q hq, m₀]
  have gyu : ∀ p < 2, Good l u.mem B M l.oY p := fun p hp =>
    (gy p hp).of_out2 hl hp fu (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])
  have vyu : ∀ p < 2, val52 l u.mem B (l.D * p + l.oY) = val52 l s.mem B (l.D * p + l.oY) := fun p hp =>
    fu.val hl hp (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])
  have aru : Ar l u.mem B M k := ar.of_out2 hl fu (by omega_using [o2, o4]) (by omega_using [o4, o10])
  refine WP.loop (M := isa) (fun n t => n = 1 ∧ t = u) ?_ 1 u ⟨rfl, rfl⟩
  intro n t ⟨hn, ht⟩
  subst hn ht
  refine WP.seq (WP.mono (r15Cmp_ok (by decide) hu.r15) fun t₀ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  refine WP.seq (WP.ite true (by rw [e₁]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h))
  have hm := amm2_ok hl (o := l.oY) (a := l.oY) (b := l.oS) (by rw [g₁]; exact hBu) (hsu.congr wr₁) (m₁ ▸ aru)
    (by omega_using [o2, o10]) (by omega_using []) (by omega_using [o2, o10]) (by omega_using [o4, o10])
    (fun p hp => m₁ ▸ gyu p hp) (fun p hp => m₁ ▸ gsu p hp)
  rw [amm_winSetup, WP.seq_iff] at hm
  refine WP.mono hm fun w hw => WP.seq (WP.mono hw fun t₁ ⟨v₁, f₁, ar₁, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have r15₁ : t₁.gpr .r15 = BitVec.ofNat 64 1 := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), g₁]; exact hu.r15
  refine WP.mono (r15Dec_ok (by decide) (by decide) r15₁) fun t₂ ⟨r15₂, z₂, k₂, me₂, x₃⟩ => ?_
  simp only [eval, z₂, Option.map_some]
  refine .inl ⟨by simp, fun p hp => ?_, ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 => ?_, ?_, ?_, ?_⟩
  · rw [me₂, ← vyu p hp, ← vsu p hp, ← m₁]; exact v₁ p hp
  · rw [me₂, ← m₀]
    exact (OutW.ofS hu.frame).trans (OutW.ofY (m₁ ▸ f₁))
  · rw [k₂.gpr (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), g₁]; exact hu.r14
  · rw [k₂.gpr (by simp [r11]), g₂ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₁, hu.gpr r r10 r11, g₀]
  · rw [k₂.2.1, rd₂, rd₁, hu.rd, rd₀]
  · rw [k₂.2.2, wr₂, wr₁, hu.wr, wr₀]
  · rw [x₃, x₂, x₁, hu.mxcsr, x₀]

end VG.Proof.Bignum.X86_64.Ifma
