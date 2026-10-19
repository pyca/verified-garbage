module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Out
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.RoundsVL

/-!
# ChaCha20 on x86-64 with AVX2: two blocks at counters `0` and `c`

`last1`'s code around the rounds computes the blocks at the counters of the
state at `rdi` plus the lane increments in `buf` (`r9`): `0, 1` (`Incs`).
With the increments `0, c` (`IncsC`) the same code computes the blocks at
counters `0` and `c`: ChaCha20-Poly1305's prologue uses it for the one-time
key's block and the block of the data's last bytes.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init xidx xidx_lt xidx_zreg stateAt_get byte_dword add_ofNat')
open VG.Proof.ChaCha20.X86_64.Avx512Tail (bsize regn baseR wregs Ctx S0 byte_out)
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)
open VG.Proof.ChaCha20.X86_64.Avx2 (ctr_get Consts)

/-- The counter of lane `l` of the first set: `0` or `c`. -/
def cOf (c l : Nat) : Nat := if l = 0 then 0 else c

/-- The first set's lane increments in `buf`: `0` and `c`, each in doubleword
0 of a lane, from `buf + 224`. -/
def IncsC (m : Mem) (buf : Addr) (c : Nat) : Prop :=
  ∀ p < 8, m.readW (buf + BitVec.ofNat 64 (4 * (56 + p))) 32 = if p = 4 then BitVec.ofNat 32 c else 0

theorem incsC_frame {buf : Addr} {c : Nat} {m m' : Mem} {rs : List Region} (h : IncsC m buf c)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨buf + BitVec.ofNat 64 224, 32⟩ : Region).Disjoint r) :
    IncsC m' buf c := by
  intro p hp
  rw [← h p hp]
  refine hf.readW ?_ hd (by decide)
  rw [show 4 * (56 + p) = 224 + 4 * p by omega, ← VG.Proof.ChaCha20.X86_64.Avx2.add_ofNat]
  exact Offset.contains_base _ (by omega) (by omega)

section
variable {D : Nat} {s : State} {c : Nat}

theorem inT_evalC (hi : IncsC s.mem (s.gpr .r9) c) {i l : Nat} (hi16 : i < 16) (hl : l < 2) :
    T.eval D s (inT 0 i l) = (ctr (S0 s) (cOf c l))[i] := by
  rw [ctr_get _ _ _ hi16]
  simp only [inT]
  have e := hi (4 * l + i % 4) (by omega)
  rw [show 56 + 8 * 0 + 4 * l + i % 4 = 56 + (4 * l + i % 4) by omega]
  split
  · simp only [T.eval, regn, baseR, e, stateAt_get _ _ hi16]
    by_cases h12 : i = 12
    · subst h12
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · simp [cOf]
      · simp [cOf]
    · rw [ite_eq_right (by omega), ite_eq_right h12]; exact BitVec.add_zero _
  · simp only [T.eval, regn, baseR, stateAt_get _ _ hi16]
    rw [ite_eq_right (by omega)]

/-- The block of lane `l` of the first set: the rounds' words `vs l` plus its
input state. -/
abbrev plusC (vs : Nat → CState) (S : CState) (c l : Nat) : CState :=
  Vector.zipWith (· + ·) (vs l) (ctr S (cOf c l))

theorem outT_evalC {vs : Nat → CState} (hz : HB 1 vs s) (hi : IncsC s.mem (s.gpr .r9) c) {i l : Nat}
    (hi16 : i < 16) (hl : l < 2) :
    T.eval D s (outT 0 i l) = (plusC vs (S0 s) c l)[i] := by
  simp only [outT, plusC, Vector.getElem_zipWith]
  rw [← inT_evalC (D := D) hi hi16 hl]
  simp only [T.eval, yw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega]
  have := hz 0 (by decide) l hl i hi16
  simp only [Nat.mul_zero, Nat.zero_add] at this ⊢
  rw [this]

end

theorem setup1C_ok {s : State} {c : Nat} (hc : Ctx 0 s) (hm : Consts s.mem (s.gpr .r9))
    (hi : IncsC s.mem (s.gpr .r9) c) :
    WP isa (.block setup1) s fun s' =>
      HB 1 (fun j => ctr (S0 s) (cOf c j)) s' ∧ YM s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have e := setup1Check_eq
  unfold setup1Check at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup1 (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      ym_of h e.1.2 hm, h.clean e.1.1, h.gpr, h.rd, h.wr⟩
    obtain rfl : k = 0 := by omega
    have r := h.reg (zreg (4 * 0 + i / 4)) (4 * l + i % 4) (by omega)
    rw [xidx_zreg _ (by omega), e.2 _ (by omega) _ (by omega)] at r
    simp only [yw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega,
      show 4 * (4 * 0 + i / 4) + i % 4 = i by omega] at r
    rw [r, inT_evalC hi hi16 hl, Nat.mul_zero, Nat.zero_add]
  · cases e

theorem last1C_ok {s : State} {c : Nat} (hc : Ctx 0 s) (hi : IncsC s.mem (s.gpr .r9) c) {vs : Nat → CState}
    (hz : HB 1 vs s) :
    WP isa (.block (addIn1 ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0)) s fun s' =>
      (∀ k < 128, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) =
        (serialize (plusC vs (S0 s) c (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 0 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := last1Check_eq
  unfold last1Check at e
  split at e
  · rename_i σ hr
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 0 s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
      h.rd, h.wr⟩
    refine byte_out (f := fun l => plusC vs (S0 s) c l) ?_
    have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega)
    rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, e _ (by omega) _ (by omega),
      outT_evalC hz hi (by omega) (by omega)] at d
    simp only [regn, baseR] at d
    rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega] at d
    exact d
  · cases e

/-- Ten double rounds `R` of `S` sets: the state's rounds, and `rax` the only
general-purpose register written (as a loop's counter). -/
def RoundsOk (S : Nat) (R : Prog isa) : Prop :=
  ∀ vs s₀, HB S vs s₀ → YM s₀ → WP isa R s₀ fun s =>
    HB S (fun j => Nat.repeat Spec.ChaCha20.innerBlock 10 (vs j)) s ∧ YM s ∧ (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧
      s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

theorem roundsS_roundsOk (vl : Bool) {S : Nat} (hS : S = 1 ∨ S = 2) : RoundsOk S (roundsS vl S 10) :=
  fun _ _ h hm => WP.mono (roundsS_ok vl hS h hm 10) fun _ ⟨h', hm', f⟩ =>
    ⟨h', hm', fun _ _ => by rw [f.gpr], f.mem, f.rd, f.wr⟩

/-- Writes of `rax` keep the regions of `Avx2Tail`'s code. -/
theorem regn_rax {D : Nat} {s s' : State} (h : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r) (b : Nat) :
    regn D s' b = regn D s b := by
  have e : s'.gpr (baseR b) = s.gpr (baseR b) := h _ (by unfold baseR; split <;> decide)
  simp only [regn, e]

theorem ctx_rax {D : Nat} {s s' : State} (hc : Ctx D s) (h : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r)
    (hwr : s'.wr = s.wr) : Ctx D s' :=
  ⟨fun b i n hb hi hn => by rw [regn_rax h, hwr]; exact hc.w b i n hb hi hn,
    fun b b' hb hb' ne => by rw [regn_rax h, regn_rax h]; exact hc.d b b' hb hb' ne, hc.small⟩

/-- The two blocks: at counters `0` and `c` from the state at `rdi`, into
`buf[0, 128)`, by the rounds `R`. -/
theorem twoC_ok {R : Prog isa} (hR : RoundsOk 1 R) {s : State} {c : Nat} (hc : Ctx 0 s)
    (hm : Consts s.mem (s.gpr .r9)) (hi : IncsC s.mem (s.gpr .r9) c) :
    WP isa (.seq (.block setup1) (.seq R (.block (addIn1 ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0))))
      s fun s' =>
      (∀ k < 128, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) =
        (serialize (Spec.ChaCha20.block (ctr (S0 s) (cOf c (k / 64))))).getD (k % 64) 0) ∧
      Frame (wregs 0 s) s.mem s'.mem ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  refine WP.seq (WP.mono (setup1C_ok hc hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (hR _ _ hz₁ ym₁) fun s₂ ⟨hz₂, _, g₂', m₂', rd₂', wr₂'⟩ => ?_)
  have g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s.gpr r := fun r h => by rw [g₂' r h, g₁]
  have m₂ : s₂.mem = s.mem := m₂'.trans m₁
  have hc₂ : Ctx 0 s₂ := ctx_rax hc g₂ (wr₂'.trans wr₁)
  have r9₂ : s₂.gpr .r9 = s.gpr .r9 := g₂ _ (by decide)
  have hi₂ : IncsC s₂.mem (s₂.gpr .r9) c := by rw [m₂, r9₂]; exact hi
  refine WP.mono (last1C_ok hc₂ hi₂ hz₂) fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ⟨fun k hk => ?_, ?_,
    fun r h => by rw [g₃, g₂ r h], rd₃.trans (rd₂'.trans rd₁), wr₃.trans (wr₂'.trans wr₁)⟩
  · have hS : S0 s₂ = S0 s := by simp only [S0, g₂ .rdi (by decide), m₂]
    rw [show s.gpr .r9 = s₂.gpr .r9 from r9₂.symm, b₃ k hk, hS]
    rfl
  · have ws : wregs 0 s₂ = wregs 0 s := by simp only [wregs, r9₂, g₂ .rsi (by decide)]
    rw [← ws, ← m₂]; exact f₃

/-! ## Four blocks at counters `0, c, c + 1, c + 2`

`last`'s code around the rounds of both sets, with the lane increments
`0, c` and `c + 1, c + 2` (`IncsC4`): the prologue's one-time key's block and
the three blocks of the data's last 65 to 192 bytes. -/

/-- The counter of block `j` (lane `j % 2` of set `j / 2`): `0`, or
`c + j - 1`. -/
def cOf4 (c j : Nat) : Nat := if j = 0 then 0 else c + j - 1

/-- Both sets' lane increments in `buf`: `0, c` and `c + 1, c + 2`, each in
doubleword 0 of a lane, from `buf + 224`. -/
def IncsC4 (m : Mem) (buf : Addr) (c : Nat) : Prop :=
  ∀ k < 2, ∀ p < 8, m.readW (buf + BitVec.ofNat 64 (4 * (56 + 8 * k + p))) 32 =
    if p % 4 = 0 then BitVec.ofNat 32 (cOf4 c (2 * k + p / 4)) else 0

theorem incsC4_frame {buf : Addr} {c : Nat} {m m' : Mem} {rs : List Region} (h : IncsC4 m buf c)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨buf + BitVec.ofNat 64 224, 64⟩ : Region).Disjoint r) :
    IncsC4 m' buf c := by
  intro k hk p hp
  rw [← h k hk p hp]
  refine hf.readW ?_ hd (by decide)
  rw [show 4 * (56 + 8 * k + p) = 224 + 4 * (8 * k + p) by omega, ← VG.Proof.ChaCha20.X86_64.Avx2.add_ofNat]
  exact Offset.contains_base _ (by omega) (by omega)

section
variable {D : Nat} {s : State} {c : Nat}

theorem inT_evalC4 (hi : IncsC4 s.mem (s.gpr .r9) c) {k i l : Nat} (hk : k < 2) (hi16 : i < 16) (hl : l < 2) :
    T.eval D s (inT k i l) = (ctr (S0 s) (cOf4 c (2 * k + l)))[i] := by
  rw [ctr_get _ _ _ hi16]
  simp only [inT]
  have e := hi k hk (4 * l + i % 4) (by omega)
  rw [show 56 + 8 * k + (4 * l + i % 4) = 56 + 8 * k + 4 * l + i % 4 by omega,
    show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega] at e
  split
  · simp only [T.eval, regn, baseR, e, stateAt_get _ _ hi16]
    by_cases h12 : i = 12
    · subst h12; simp
    · rw [ite_eq_right (by omega), ite_eq_right h12]; exact BitVec.add_zero _
  · simp only [T.eval, regn, baseR, stateAt_get _ _ hi16]
    rw [ite_eq_right (by omega)]

/-- Block `j` of the two sets: the rounds' words `vs j` plus its input state. -/
abbrev plusC4 (vs : Nat → CState) (S : CState) (c j : Nat) : CState :=
  Vector.zipWith (· + ·) (vs j) (ctr S (cOf4 c j))

theorem outT_evalC4 {vs : Nat → CState} (hz : HB 2 vs s) (hi : IncsC4 s.mem (s.gpr .r9) c) {k i l : Nat}
    (hk : k < 2) (hi16 : i < 16) (hl : l < 2) :
    T.eval D s (outT k i l) = (plusC4 vs (S0 s) c (2 * k + l))[i] := by
  simp only [outT, plusC4, Vector.getElem_zipWith]
  rw [← inT_evalC4 (D := D) hi hk hi16 hl]
  simp only [T.eval, yw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega]
  rw [hz k hk l hl i hi16]

end

theorem setupC4_ok {s : State} {c : Nat} (hc : Ctx 0 s) (hm : Consts s.mem (s.gpr .r9))
    (hi : IncsC4 s.mem (s.gpr .r9) c) :
    WP isa (.block setup) s fun s' =>
      HB 2 (fun j => ctr (S0 s) (cOf4 c j)) s' ∧ YM s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have e := setupCheck_0
  unfold setupCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      ym_of h e.1.2 hm, h.clean e.1.1, h.gpr, h.rd, h.wr⟩
    have r := h.reg (zreg (4 * k + i / 4)) (4 * l + i % 4) (by omega)
    rw [xidx_zreg _ (by omega), e.2 k hk _ (by omega) _ (by omega)] at r
    simp only [yw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega,
      show 4 * (i / 4) + i % 4 = i by omega] at r
    rw [r, inT_evalC4 hi hk hi16 hl]
  · cases e

theorem lastC4_ok {s : State} {c : Nat} (hc : Ctx 0 s) (hi : IncsC4 s.mem (s.gpr .r9) c) {vs : Nat → CState}
    (hz : HB 2 vs s) :
    WP isa (.block (addIn ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++ storeSet .xmm4 .xmm5 .xmm6 .xmm7 128)) s
      fun s' =>
      (∀ k < 256, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) =
        (serialize (plusC4 vs (S0 s) c (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 0 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := lastCheck_eq
  unfold lastCheck at e
  split at e
  · rename_i σ hr
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 0 s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
      h.rd, h.wr⟩
    refine byte_out (f := fun j => plusC4 vs (S0 s) c j) ?_
    have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega)
    rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, e _ (by omega) _ (by omega),
      outT_evalC4 hz hi (by omega) (by omega) (by omega),
      show 2 * (k / 64 / 2) + k / 64 % 2 = k / 64 by omega] at d
    simp only [regn, baseR] at d
    rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega] at d
    exact d
  · cases e

/-- The four blocks: at counters `0, c, c + 1, c + 2` from the state at
`rdi`, into `buf[0, 256)`. -/
theorem fourC_ok {R : Prog isa} (hR : RoundsOk 2 R) {s : State} {c : Nat} (hc : Ctx 0 s)
    (hm : Consts s.mem (s.gpr .r9)) (hi : IncsC4 s.mem (s.gpr .r9) c) :
    WP isa (.seq (.block setup) (.seq R
      (.block (addIn ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++ storeSet .xmm4 .xmm5 .xmm6 .xmm7 128)))) s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) =
        (serialize (Spec.ChaCha20.block (ctr (S0 s) (cOf4 c (k / 64))))).getD (k % 64) 0) ∧
      Frame (wregs 0 s) s.mem s'.mem ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  refine WP.seq (WP.mono (setupC4_ok hc hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (hR _ _ hz₁ ym₁) fun s₂ ⟨hz₂, _, g₂', m₂', rd₂', wr₂'⟩ => ?_)
  have g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s.gpr r := fun r h => by rw [g₂' r h, g₁]
  have m₂ : s₂.mem = s.mem := m₂'.trans m₁
  have hc₂ : Ctx 0 s₂ := ctx_rax hc g₂ (wr₂'.trans wr₁)
  have r9₂ : s₂.gpr .r9 = s.gpr .r9 := g₂ _ (by decide)
  have hi₂ : IncsC4 s₂.mem (s₂.gpr .r9) c := by rw [m₂, r9₂]; exact hi
  refine WP.mono (lastC4_ok hc₂ hi₂ hz₂) fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ⟨fun k hk => ?_, ?_,
    fun r h => by rw [g₃, g₂ r h], rd₃.trans (rd₂'.trans rd₁), wr₃.trans (wr₂'.trans wr₁)⟩
  · have hS : S0 s₂ = S0 s := by simp only [S0, g₂ .rdi (by decide), m₂]
    rw [show s.gpr .r9 = s₂.gpr .r9 from r9₂.symm, b₃ k hk, hS]
    rfl
  · have ws : wregs 0 s₂ = wregs 0 s := by simp only [wregs, r9₂, g₂ .rsi (by decide)]
    rw [← ws, ← m₂]; exact f₃

end VG.Proof.ChaCha20.X86_64.Avx2Tail
