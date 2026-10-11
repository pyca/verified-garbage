import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas

/-!
# RSA with AVX512_IFMA on x86-64, any size: the vector code

`vec` (`vec_ok`), within Intel's MXCSR prologue
and epilogue (the caller's MXCSR saved at `oMx`, `0x1FBF` loaded, and the
saved value, bits 31:16 cleared, restored), `X` and `Y` into Montgomery
form for `R = 2^(208 R)` (by `K1 ≡ 2^(416 R - 64 W)`, as they hold
`x 2^(64 W)` and `2^(64 W)`), the exponentiations, and `Y := Y Fin / R`:
`Y ≡ x^e Fin`.
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (wp_seqs_app ofs_off0 and_ffff_hi mont_into0 mont_into1 mont_out
  writeW32_outside se_ofNat)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The prologue's first half: the caller's MXCSR, bits 31:16 cleared, at `oMx`. -/
theorem mxSave_ok {s : State} {B : Addr} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D + 8)) :
    WP isa (.block [.stmxcsr (at_ .rbx l.oMx), .mov32 .r11 (.mem (at_ .rbx l.oMx)), .alu32 .and .r11 (.imm 0xFFFF),
        .store32 (at_ .rbx l.oMx) .r11]) s fun s' =>
      s'.mem = (s.mem.writeW (off B l.oMx) s.mxcsr).writeW (off B l.oMx) (s.mxcsr &&& 0xFFFF) ∧
      VG.Proof.MlKem.X86_64.Keep [.r11] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 l.oMx) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := l.oMx) (n := 4) (by simp only [Lay.oMx]; omega_using []) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 l.oMx) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := l.oMx) (n := 4) (by simp only [Lay.oMx]; omega_using []) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r11] (Q := fun s' =>
    s'.mem = (s.mem.writeW (off B l.oMx) s.mxcsr).writeW (off B l.oMx) (s.mxcsr &&& 0xFFFF) ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [eaG', hB, hst, hld, Mem.readW_writeW_self32]
    and_intros <;> rfl) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

/-- The prologue's second half: `MXCSR := 0x1FBF`. -/
theorem mxSet_ok {s : State} {B : Addr} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D + 8)) :
    WP isa (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (l.oMx + 4)) .rax,
        .ldmxcsr (at_ .rbx (l.oMx + 4)), .lfence]) s fun s' =>
      s'.mem = s.mem.writeW (off B (l.oMx + 4)) (0x1FBF : BitVec 32) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = 0x1FBF := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 (l.oMx + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := l.oMx + 4) (n := 4) (by simp only [Lay.oMx]; omega_using []) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (l.oMx + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := l.oMx + 4) (n := 4) (by simp only [Lay.oMx]; omega_using []) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' =>
    s'.mem = s.mem.writeW (off B (l.oMx + 4)) (0x1FBF : BitVec 32) ∧ s'.mxcsr = 0x1FBF) (by
    xrun [eaG', hB, hst, hld, Mem.readW_writeW_self32]) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

/-- The epilogue: the saved MXCSR. -/
theorem mxRestore_ok {s : State} {B : Addr} {v : BitVec 32} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D + 8))
    (hv : s.mem.readW (off B l.oMx) 32 = v &&& 0xFFFF) :
    WP isa (.block [.ldmxcsr (at_ .rbx l.oMx), .vop .vzeroupper]) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = v &&& 0xFFFF := by
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 l.oMx) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := l.oMx) (n := 4) (by simp only [Lay.oMx]; omega_using []) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  rw [WP.block_cons_iff]
  refine ⟨{ s with mxcsr := v &&& 0xFFFF }, ?_, ?_⟩
  · simp only [exec, eaG', hB, State.load32, hld, ite_true, Option.bind_some]
    rw [show s.mem.readW (B + BitVec.ofNat 64 l.oMx) 32 = v &&& 0xFFFF from hv, and_ffff_hi]; rfl
  · rw [WP.block_cons_iff]
    exact ⟨_, rfl, WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem Out2.toOutside {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m')
    (hon : o + n ≤ l.D) : Outside B 0 (2 * l.D) m m' := fun a ha => h a fun p hp => by
  rcases ha with ha | ha
  · omega_using [ha]
  · have : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
    exact .inr (by omega_using [hon, ha, this])

theorem OutE.toOutside {B : Addr} {m m' : Mem} (h : OutE l B m m') : Outside B 0 (2 * l.D) m m' :=
  fun a ha => h a fun p hp => by
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
    rcases ha with ha | ha
    · omega_using [ha]
    · have : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
      exact ⟨.inr (by omega_using [o2, o10, ha, this]), .inr (by omega_using [o4, o10, ha, this]), .inr
          (by omega_using [o8, o10, ha, this]), .inr (by omega_using [o5, o10, ha, this])⟩

theorem OutE.word_at {B : Addr} {m m' : Mem} (h : OutE l B m m') {p c : Nat} (hp : p < 2)
    (hY : c + 8 ≤ l.oY ∨ l.oY + l.NB ≤ c) (hS : c + 8 ≤ l.oS ∨ l.oS + l.NB ≤ c) (hV : c + 8 ≤ l.oV ∨ l.oV + 8 ≤ c)
    (hT : c + 8 ≤ l.oTab ∨ l.oTab + 16 * l.NB ≤ c) (hcD : c + 8 ≤ l.D) (hD : l.D + l.NB ≤ 2 ^ 20) :
    word m' B (l.D * p + c) = word m B (l.D * p + c) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine (Mem.readW_congr fun i hi => (h _ fun p' hp' => ?_).symm).symm
  rw [ofs_off B (by rcases D_mul (l := l) hp with h | h <;> omega_using [hcD, hD, hi, h])]
  have : i < 8 := hi
  rcases D_mul (l := l) hp with h1 | h1 <;> rcases D_mul (l := l) hp' with h2 | h2 <;> omega_using [hY, hS, hV, hT,
      this, h1, h2, hcD, o2, o4, o5, o8, o10]

theorem Good.of_outE (hl : LayOk l) {m m' : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : Good l m B M c p)
    (hp : p < 2) (h : OutE l B m m')
    (hY : c + l.NB ≤ l.oY ∨ l.oY + l.NB ≤ c) (hS : c + l.NB ≤ l.oS ∨ l.oS + l.NB ≤ c)
    (hV : c + l.NB ≤ l.oV ∨ l.oV + 8 ≤ c) (hT : c + l.NB ≤ l.oTab ∨ l.oTab + 16 * l.NB ≤ c)
    (hcD : c + l.NB ≤ l.D) :
    Good l m' B M c p ∧ val52 l m' B (l.D * p + c) = val52 l m B (l.D * p + c) := by
  have e : ∀ j < l.L, limb l m' B (l.D * p + c) j = limb l m B (l.D * p + c) j := fun j hj => by
    have := off_lt hl hj
    show (word m' B _).toNat = (word m B _).toNat
    rw [Nat.add_assoc, h.word_at hp (by omega_using [hY, this]) (by omega_using [hS, this]) (by omega_using [hV, this])
        (by omega_using [hT, this]) (by omega_using [hcD, this]) hl.D_bounds.2]
  exact ⟨g.of_limbs e, val52_of_limbs e⟩

theorem Out2.byte (hl : LayOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {p i : Nat}
    (hp : p < 2) (hi : i < l.E) (ho : o + n ≤ l.oE ∨ l.oE + l.E ≤ o) (hoD : o + n ≤ l.D) :
    m' (off B (l.D * p + l.oE + i)) = m (off B (l.D * p + l.oE + i)) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  refine h _ fun p' hp' => ?_
  rw [ofs_off0 B (by rcases D_mul (l := l) hp with h | h <;> omega_using [hi, o6, o10, hD, h])]
  rcases D_mul (l := l) hp with h1 | h1 <;> rcases D_mul (l := l) hp' with h2 | h2 <;> omega_using [hi, ho, h1, h2, o6, o10, hoD]

theorem dbl_le (hl : LayOk l) : 64 * l.W ≤ 416 * l.R := by rcases hl with rfl | rfl | rfl <;> decide

/-- The head of `k1Body`: the operands at `r13` and `oK1`. -/
theorem k1Head_ok (hl : LayOk l) {s : State} {B : Addr} {o : Nat}
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 o) :
    WP isa (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .mov .r9 (.reg .rbx),
        .alu .add .r9 (.imm (BitVec.ofNat 32 l.oK1)), .mov .r11 (.reg .rbx), .alu .add .r11 (.reg .r13)]) s
      fun s' => s'.gpr .r8 = off B o ∧ s'.gpr .r9 = off B l.oK1 ∧ s'.gpr .r11 = off B o ∧
        VG.Proof.MlKem.X86_64.Keep [.r8, .r9, .r11] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8, .r9, .r11] (Q := fun s' =>
    s'.gpr .r8 = off B o ∧ s'.gpr .r9 = off B l.oK1 ∧ s'.gpr .r11 = off B o ∧
      s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr) (by
    xrun [hB, h13, se_ofNat (show l.oK1 < 2 ^ 31 by omega_using [hD, o7, o10])]
    and_intros
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d, e⟩, k⟩ => ⟨a, b, c, k, d, e⟩

/-- The tail of `k1Body`: `r13` to the next number, `ZF` after `X`. -/
theorem k1Tail_ok (hl : LayOk l) {s : State} {o : Nat} (ho : o = l.oY ∨ o = l.oX)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 o) :
    WP isa (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 l.NB)),
        .alu .cmp .r13 (.imm (BitVec.ofNat 32 l.oS))]) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (o + l.NB) ∧ s'.zf = some (decide (o = l.oX)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r13] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  have hNB := NB_le hl
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun s' =>
    s'.gpr .r13 = BitVec.ofNat 64 (o + l.NB) ∧ s'.zf = some (decide (o = l.oX)) ∧
      s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr) (by
    xrun [h13, se_ofNat (show l.NB < 2 ^ 31 by omega_using [hD]),
      se_ofNat (show l.oS < 2 ^ 31 by omega_using [hD, o4, o10])]
    and_intros
    · rw [← BitVec.ofNat_add]
    · rw [← BitVec.ofNat_add, ofNat_sub_beq (by omega_using [hD, o2, o3, ho]) (by omega_using [hD, o4])]
      refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
      · rcases ho with rfl | rfl <;> omega_using [h, o2, o3, o4, hNB]
      · omega_using [h, o3, o4]
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, k, c, d⟩

/-- What `[o] := [o] [oK1] 2^(-208 R)` leaves, from `s`. -/
structure K1Post (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (M k : Nat → Nat) (o : Nat)
    (s t : State) : Prop where
  v : ∀ p < 2, Good l t.mem B M o p ∧ val52 l t.mem B (l.D * p + o) * 2 ^ (52 * l.L) % M p =
    val52 l s.mem B (l.D * p + o) * val52 l s.mem B (l.D * p + l.oK1) % M p
  f : Out2 l B o l.NB s.mem t.mem
  ar : Ar l t.mem B M k
  g : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
    r ≠ .r12 → r ≠ .r13 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

/-- One iteration of the conversions' loop: `[o] := [o] [oK1] 2^(-208 R)`. -/
theorem k1Iter_ok (hl : LayOk l) {s : State} {B : Addr} {M k : Nat → Nat} {o : Nat}
    (ho : o = l.oY ∨ o = l.oX) (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 o)
    (hs : Scr s B (2 * l.D)) (ar : Ar l s.mem B M k)
    (ga : ∀ p < 2, Good l s.mem B M o p) (gk : ∀ p < 2, Good l s.mem B M l.oK1 p) :
    WP isa (k1Body l) s fun t => K1Post l B M k o s t ∧ t.gpr .r13 = BitVec.ofNat 64 (o + l.NB) ∧
      t.zf = some (decide (o = l.oX)) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.seq (WP.mono (k1Head_ok hl hB h13) fun t₁ ⟨h8, h9, h11, k₁, me₁, x₁⟩ => ?_)
  have rbx₁ : t₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB
  refine WP.seq (WP.mono (ammCore2_ok hl (o := o) (a := o) (b := l.oK1) (M := M) (k := k) rbx₁ h8 h9 h11
      (hs.congr k₁.2.2) (by rw [me₁]; exact ar) (by omega_using [ho, o2, o3, o10])
      (by omega_using [ho, o2, o3]) (by omega_using [ho, o2, o3, o10]) (by omega_using [o7, o10])
      (by rw [me₁]; exact ga) (by rw [me₁]; exact gk))
    fun t₂ ⟨v₂, f₂, ar₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have r13₂ : t₂.gpr .r13 = BitVec.ofNat 64 o := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁.gpr (by decide)]; exact h13
  refine WP.mono (k1Tail_ok hl ho r13₂) fun t₃ ⟨r13₃, z₃, k₃, me₃, x₃⟩ =>
    ⟨⟨fun p hp => ?_, ?_, by rw [me₃]; exact ar₂, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_,
      by rw [k₃.2.1, rd₂, k₁.2.1], by rw [k₃.2.2, wr₂, k₁.2.2], by rw [x₃, x₂, x₁]⟩, r13₃, z₃⟩
  · rw [me₃]; have e := v₂ p hp; rw [me₁] at e; exact e
  · rw [me₃, ← me₁]; exact f₂
  · rw [k₃.gpr (by simp [r10]), g₂ r r1 r2 r3 r4 r6 r7 r9, k₁.gpr (by simp [r5, r6, r8])]

/-- The conversions' loop: `Y`, then `X`. -/
theorem k1Loop_ok (hl : LayOk l) {s : State} {B : Addr} {M k : Nat → Nat} (hB : s.gpr .rbx = B)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 l.oY) (hs : Scr s B (2 * l.D)) (ar : Ar l s.mem B M k)
    (gx : ∀ p < 2, Good l s.mem B M l.oX p) (gy : ∀ p < 2, Good l s.mem B M l.oY p)
    (gk : ∀ p < 2, Good l s.mem B M l.oK1 p) :
    WP isa (.loop (k1Body l) .ne) s fun t =>
      ∃ s₁, K1Post l B M k l.oY s s₁ ∧ K1Post l B M k l.oX s₁ t := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  refine WP.loop (M := isa) (fun n t => (n = 2 ∧ t = s) ∨ (n = 1 ∧ K1Post l B M k l.oY s t ∧
      t.gpr .r13 = BitVec.ofNat 64 l.oX)) ?_ 2 s (.inl ⟨rfl, rfl⟩)
  rintro n t (⟨rfl, rfl⟩ | ⟨rfl, hp, h13'⟩)
  · refine WP.mono (k1Iter_ok hl (.inl rfl) hB h13 hs ar gy gk) fun t₁ ⟨hp₁, r13₁, z₁⟩ => .inr ⟨?_, 1,
      by decide, .inr ⟨rfl, hp₁, ?_⟩⟩
    · simp only [eval, z₁, Option.map_some]
      simp only [decide_eq_false (show ¬ l.oY = l.oX by omega_using [o2, o3, NB_le hl]),
        Bool.not_false]
    · rw [r13₁, show l.oY + l.NB = l.oX by omega_using [o2, o3]]
  · have hB' : t.gpr .rbx = B := by
      rw [hp.g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact hB
    refine WP.mono (k1Iter_ok hl (.inr rfl) hB' h13' (hs.congr hp.wr) hp.ar
      (fun p hp' => (gx p hp').of_out2 hl hp' hp.f (.inr (by omega_using [o2, o3]))
        (by omega_using [o3, o10]) (by omega_using [o2, o10]))
      (fun p hp' => (gk p hp').of_out2 hl hp' hp.f (.inr (by omega_using [o2, o7]))
        (by omega_using [o7, o10]) (by omega_using [o2, o10])))
      fun t₁ ⟨hp₁, _, z₁⟩ => .inl ⟨?_, t, hp, hp₁⟩
    simp only [eval, z₁, Option.map_some, decide_true, Bool.not_true]

/-- The vector code inside the MXCSR prologue and epilogue. -/
theorem vecBody_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * l.D)) (ar : Ar l s.mem B M k) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p))
    (gx : ∀ p < 2, Good l s.mem B M l.oX p) (gy : ∀ p < 2, Good l s.mem B M l.oY p)
    (gk : ∀ p < 2, Good l s.mem B M l.oK1 p) (gf : ∀ p < 2, Good l s.mem B M l.oFin p)
    (vx : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oX) % M p = x p * 2 ^ (64 * l.W) % M p)
    (vy : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ (64 * l.W) % M p)
    (vk : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oK1) % M p = 2 ^ (416 * l.R - 64 * l.W) % M p) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (([.block [.mov32 .r13 (.imm (BitVec.ofNat 32 l.oY))],
        .loop (k1Body l) .ne] : List (Prog isa)) ++ expLoop l ++
        ([amm l l.oY l.oY l.oFin] : List (Prog isa)))) s fun s' =>
      (∀ p < 2, Good l s'.mem B M l.oY p ∧
        (Q → val52 l s'.mem B (l.D * p + l.oY) % M p =
          x p ^ ev l s.mem B p l.E * val52 l s.mem B (l.D * p + l.oFin) % M p)) ∧
      Outside B 0 (2 * l.D) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hE : 1 ≤ l.E := E_pos hl
  have e2 : 2 ^ (64 * l.W) * 2 ^ (416 * l.R - 64 * l.W) = 2 ^ (52 * l.L) * 2 ^ (52 * l.L) := by
    have := dbl_le hl
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; simp only [Lay.L]; omega_using [this]
  refine wp_seqs_app (by simp) (by simp) (wp_seqs_app (by simp) (by simp [expLoop, tabBuild]) ?_)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s.setReg32 .r13 (BitVec.ofNat 32 l.oY), rfl, WP.block_nil ?_⟩
  have h13 : (s.setReg32 .r13 (BitVec.ofNat 32 l.oY)).gpr .r13 = BitVec.ofNat 64 l.oY := by
    rw [State.setReg32, RegUpd.gpr_setReg_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hD, o2]
  have hg₀ : ∀ r, r ≠ .r13 → (s.setReg32 .r13 (BitVec.ofNat 32 l.oY)).gpr r = s.gpr r := fun r hr => by
    rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr]
  refine WP.mono (k1Loop_ok hl (by rw [hg₀ _ (by decide)]; exact hB) h13 (hs.congr rfl) ar gx gy gk)
    fun s₂ ⟨s₁, p₁, p₂⟩ => ?_
  have hB₂ : s₂.gpr .rbx = B := by
    rw [p₂.g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), p₁.g _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hg₀ _ (by decide)]
    exact hB
  have hs₂ : Scr s₂ B (2 * l.D) := hs.congr (by rw [p₂.wr, p₁.wr]; rfl)
  have ar₂ := p₂.ar
  have f₁ : Out2 l B l.oY l.NB s.mem s₁.mem := p₁.f
  have f₂ : Out2 l B l.oX l.NB s₁.mem s₂.mem := p₂.f
  have gx₂ : ∀ p < 2, Good l s₂.mem B M l.oX p := fun p hp => (p₂.v p hp).1
  have vx₂ : Q → ∀ p < 2, val52 l s₂.mem B (l.D * p + l.oX) % M p = x p ^ 1 * 2 ^ (52 * l.L) % M p :=
    fun hq p hp => by
      have e := (p₂.v p hp).2
      rw [f₁.val hl hp (.inr (by omega_using [o2, o3])) (by omega_using [o3, o10]) (by omega_using [o2, o10]),
        f₁.val hl hp (.inr (by omega_using [o2, o7])) (by omega_using [o7, o10]) (by omega_using [o2, o10])] at e
      exact mont_into1 (hR p hp) (vx hq p hp) (vk hq p hp) e2 e
  have gy₂ : ∀ p < 2, Good l s₂.mem B M l.oY p := fun p hp =>
    (p₁.v p hp).1.of_out2 hl hp f₂ (.inl (by omega_using [o2, o3])) (by omega_using [o2, o10])
      (by omega_using [o3, o10])
  have vy₂ : Q → ∀ p < 2, val52 l s₂.mem B (l.D * p + l.oY) % M p = x p ^ 0 * 2 ^ (52 * l.L) % M p :=
    fun hq p hp => by
      rw [f₂.val hl hp (.inl (by omega_using [o2, o3])) (by omega_using [o2, o10]) (by omega_using [o3, o10])]
      exact mont_into0 (hR p hp) (vy hq p hp) (vk hq p hp) e2 (p₁.v p hp).2
  refine WP.mono (expLoop_ok hl hB₂ hs₂ ar₂ hR gy₂ gx₂ vy₂ vx₂)
    fun s₃ ⟨st₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hB₃ : s₃.gpr .rbx = B := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hB₂
  -- `Fin`, unchanged
  have gf₃ : ∀ p < 2, Good l s₃.mem B M l.oFin p ∧
      val52 l s₃.mem B (l.D * p + l.oFin) = val52 l s.mem B (l.D * p + l.oFin) := fun p hp => by
    have g₁ := (gf p hp).of_out2 hl hp f₁ (.inr (by omega_using [o2, o9])) (by omega_using [o9, o10]) (by omega_using [o2, o10])
    have g₂ := g₁.of_out2 hl hp f₂ (.inr (by omega_using [o3, o9])) (by omega_using [o9, o10]) (by omega_using [o3, o10])
    obtain ⟨g₃, e₃⟩ := g₂.of_outE hl hp f₃ (.inr (by omega_using [o2, o9])) (.inr (by omega_using [o4, o9])) (.inr
        (by omega_using [o8, o9]))
      (.inr (by omega_using [o5, o9])) (by omega_using [o9, o10])
    refine ⟨g₃, ?_⟩
    rw [e₃, f₂.val hl hp (.inr (by omega_using [o3, o9])) (by omega_using [o9, o10]) (by omega_using [o3, o10]),
      f₁.val hl hp (.inr (by omega_using [o2, o9])) (by omega_using [o9, o10]) (by omega_using [o2, o10])]
  have hev : ∀ p < 2, ev l s₂.mem B p l.E = ev l s.mem B p l.E := fun p hp =>
    ev_congr l.E fun i hi => (f₂.byte hl hp hi (.inl (by omega_using [o3, o6])) (by omega_using [o3, o10])).trans
      (f₁.byte hl hp hi (.inl (by omega_using [o2, o6])) (by omega_using [o2, o10]))
  refine WP.mono (amm2_ok hl hB₃ (hs₂.congr wr₃) st₃.ar (by omega_using [o2, o10]) (by omega_using [])
      (by omega_using [o2, o10]) (by omega_using [o9, o10]) st₃.y
    (fun p hp => (gf₃ p hp).1)) fun s₄ ⟨v₄, f₄, ar₄, g₄, rd₄, wr₄, x₄⟩ =>
      ⟨fun p hp => ⟨(v₄ p hp).1, fun hq => ?_⟩, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 => ?_,
        by rw [rd₄, rd₃, p₂.rd, p₁.rd]; rfl, by rw [wr₄, wr₃, p₂.wr, p₁.wr]; rfl,
        by rw [x₄, x₃, p₂.mxcsr, p₁.mxcsr]; rfl⟩
  · have e := (v₄ p hp).2
    rw [(gf₃ p hp).2] at e
    rw [← hev p hp]
    exact mont_out (hR p hp) (st₃.yv hq p hp) e
  · exact ((f₁.toOutside (by omega_using [o2, o10])).trans (f₂.toOutside (by omega_using [o3, o10]))).trans
      (f₃.toOutside.trans (f₄.toOutside (by omega_using [o2, o10])))
  · rw [g₄ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₃ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12,
      p₂.g r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10, p₁.g r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10, hg₀ r r10]

/-! ## Writes above both regions -/

section
variable {m m' : Mem} {B : Addr} {n : Nat} (hl : LayOk l) (h : Outside B (2 * l.D) n m m')
include hl h

theorem hi_word {p c : Nat} (hp : p < 2) (hc : c + 8 ≤ l.D) : word m' B (l.D * p + c) = word m B (l.D * p + c) :=
  have := hl.D_bounds
  h.word (.inl (by rcases D_mul (l := l) hp with h | h <;> omega_using [hc, h]))
    (by rcases D_mul (l := l) hp with h | h <;> omega_using [hc, this, h])

theorem hi_limb {p c : Nat} (hp : p < 2) (hc : c + l.NB ≤ l.D) {j : Nat} (hj : j < l.L) :
    limb l m' B (l.D * p + c) j = limb l m B (l.D * p + c) j := by
  have := off_lt hl hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [Nat.add_assoc, hi_word hl h hp (by omega_using [hc, this])]

theorem hi_val {p c : Nat} (hp : p < 2) (hc : c + l.NB ≤ l.D) :
    val52 l m' B (l.D * p + c) = val52 l m B (l.D * p + c) :=
  val52_of_limbs fun _ hj => hi_limb hl h hp hc hj

theorem Good.of_hi {M : Nat → Nat} {p c : Nat} (g : Good l m B M c p) (hp : p < 2) (hc : c + l.NB ≤ l.D) :
    Good l m' B M c p :=
  g.of_limbs fun _ hj => hi_limb hl h hp hc hj

theorem Ar.of_hi {M k : Nat → Nat} (a : Ar l m B M k) : Ar l m' B M k := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have := hl.bounds
  refine ⟨fun p hp j hj => ?_, fun p hp => ?_, fun p hp t ht => ?_, a.klt, fun p hp => ?_, a.bnd⟩
  · rw [hi_limb hl h hp (by simp only [oM]; omega_using [o10]) hj]; exact a.mlt p hp j hj
  · rw [hi_val hl h hp (by simp only [oM]; omega_using [o10])]; exact a.mv p hp
  · rw [Nat.add_assoc, hi_word hl h hp (by omega_using [o1, o10, ht]), ← Nat.add_assoc]; exact a.kw p hp t ht
  · rw [hi_limb hl h hp (by simp only [oM]; omega_using [o10]) (by simp only [Lay.L]; omega_using [this])]; exact a.k0 p hp

theorem ev_of_hi {p : Nat} (hp : p < 2) : ev l m' B p l.E = ev l m B p l.E := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have := hl.D_bounds
  exact ev_congr l.E fun i hi => h _ (.inl (by
    rw [ofs_off0 B (by rcases D_mul (l := l) hp with h | h <;> omega_using [o6, o10, this, hi, h])]
    rcases D_mul (l := l) hp with h | h <;> omega_using [o6, o10, hi, h]))

end

/-- The vector code: `Y ≡ x^e Fin` for each prime. -/
theorem vec_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * l.D + 8)) (ar : Ar l s.mem B M k) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.L)) (M p))
    (gx : ∀ p < 2, Good l s.mem B M l.oX p) (gy : ∀ p < 2, Good l s.mem B M l.oY p)
    (gk : ∀ p < 2, Good l s.mem B M l.oK1 p) (gf : ∀ p < 2, Good l s.mem B M l.oFin p)
    (vx : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oX) % M p = x p * 2 ^ (64 * l.W) % M p)
    (vy : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ (64 * l.W) % M p)
    (vk : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oK1) % M p = 2 ^ (416 * l.R - 64 * l.W) % M p) :
    WP isa (vec l) s fun s' =>
      (∀ p < 2, Good l s'.mem B M l.oY p ∧
        (Q → val52 l s'.mem B (l.D * p + l.oY) % M p =
          x p ^ ev l s.mem B p l.E * val52 l s.mem B (l.D * p + l.oFin) % M p)) ∧
      Outside B 0 (2 * l.D + 8) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr &&& 0xFFFF := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hn := hs.nowrap
  have hM : l.oMx = 2 * l.D := rfl
  refine WP.seq (WP.mono (mxSave_ok hB hs) fun s₁ ⟨m₁, k₁, x₁⟩ => ?_)
  have hB₁ : s₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB
  refine WP.seq (WP.seq (WP.mono (mxSet_ok hB₁ (hs.congr k₁.2.2)) fun s₂ ⟨m₂, k₂, x₂⟩ => ?_))
  have hB₂ : s₂.gpr .rbx = B := by rw [k₂.gpr (by decide)]; exact hB₁
  have hs₂ : Scr s₂ B (2 * l.D + 8) := hs.congr (by rw [k₂.2.2, k₁.2.2])
  have O₁ : Outside B (2 * l.D) 4 s.mem s₁.mem := by
    rw [m₁, hM]
    exact (writeW32_outside _ B _ (by omega_using [hn])).trans (writeW32_outside _ B _ (by omega_using [hn]))
  have O₂ : Outside B (2 * l.D + 4) 4 s₁.mem s₂.mem := by
    rw [m₂, hM]; exact writeW32_outside _ B _ (by omega_using [hn])
  have O : Outside B (2 * l.D) 8 s.mem s₂.mem :=
    (O₁.mono (by omega_using []) (by omega_using [])).trans (O₂.mono (by omega_using []) (by omega_using []))
  refine WP.seq (WP.mono (vecBody_ok hl (Q := Q) (x := x) hB₂ (AmmSym.Scr.mono hs₂ (by omega_using [])) (Ar.of_hi hl O ar) hR
    (fun p hp => (gx p hp).of_hi hl O hp (by omega_using [o3, o10])) (fun p hp => (gy p hp).of_hi hl O hp (by omega_using [o2, o10]))
    (fun p hp => (gk p hp).of_hi hl O hp (by omega_using [o7, o10])) (fun p hp => (gf p hp).of_hi hl O hp (by omega_using [o9, o10]))
    (fun hq p hp => by rw [hi_val hl O hp (by omega_using [o3, o10])]; exact vx hq p hp)
    (fun hq p hp => by rw [hi_val hl O hp (by omega_using [o2, o10])]; exact vy hq p hp)
    (fun hq p hp => by rw [hi_val hl O hp (by omega_using [o7, o10])]; exact vk hq p hp))
    fun s₃ ⟨v₃, O₃, g₃, rd₃, wr₃, x₃⟩ => ?_)
  rw [WP.block_cons_iff]
  refine ⟨s₃, rfl, WP.block_nil ?_⟩
  have hB₃ : s₃.gpr .rbx = B := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hB₂
  have hv : s₃.mem.readW (off B l.oMx) 32 = s.mxcsr &&& 0xFFFF := by
    rw [Outside.readW32 O₃ (.inr (by omega_using [hM])) (by omega_using [hn, hM]),
      Outside.readW32 O₂ (.inl (by omega_using [hM])) (by omega_using [hn, hM]), m₁, Mem.readW_writeW_self32]
  refine WP.mono (mxRestore_ok hB₃ (hs₂.congr wr₃) hv) fun s₄ ⟨m₄, g₄, rd₄, wr₄, x₄⟩ =>
    ⟨fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 => ?_, by rw [rd₄, rd₃, k₂.2.1, k₁.2.1],
      by rw [wr₄, wr₃, k₂.2.2, k₁.2.2], x₄⟩
  · rw [m₄]
    refine ⟨(v₃ p hp).1, fun hq => ?_⟩
    rw [(v₃ p hp).2 hq, ev_of_hi hl O hp, hi_val hl O hp (by omega_using [o9, o10])]
  · rw [m₄]; exact (O.mono (by omega_using []) (by omega_using [])).trans (O₃.mono (by omega_using []) (by omega_using []))
  · rw [g₄, g₃ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12, k₂.gpr (by simp [r1]), k₁.gpr (by simp [r8])]

end VG.Proof.Bignum.X86_64.Ifma
