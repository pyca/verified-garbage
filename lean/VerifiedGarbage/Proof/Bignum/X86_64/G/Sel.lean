import VerifiedGarbage.Proof.Bignum.X86_64.G.Spec
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaSel

/-!
# RSA with AVX512_IFMA on x86-64, any size: reading an entry of the table

`IfmaSel` for `CrtIfmaG`: `select l p` reads the top 4 bits `v` of the
quadword at `oV` of prime `p`'s region and copies entry `v` of the table
(`NB` bytes at `oTab + NB v`) to `oS`, reading every entry and keeping entry
`v` under a mask (`select_ok`). The vector part of an iteration is run by
`ESym` and checked for each layout (`checkSel`).
-/

namespace VG.Proof.Bignum.X86_64.G

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off)
open VG.Impl.Rsa.X86_64.CrtIfmaG
open VG.Proof.Bignum.X86_64.AmmSym (Ctx Keeps selMask selMask_ok selMask_and zero_or64 or_zero64 shr60
  wrList wrList_outside' word_wrList_unique off_add setOff)
open VG.Proof.MlKem.X86_64 (Keep)

variable {l : Lay}

theorem ea_rG {s : State} {r : Reg} {a : Addr} (h : s.gpr r = a) (d : Nat) :
    s.ea (at_ r d) = a + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, h]
  exact congrArg _ (BitVec.ofInt_natCast ..)

theorem vreg_lo : ∀ k < 16, ∃ x, vreg k = .lo x := by
  intro k hk
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | exact ⟨_, rfl⟩ | omega

theorem qv_lo {s s' : State} (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) {k : Nat} (hk : k < 16) (j : Nat) :
    qv s' (vreg k) j = qv s (vreg k) j := by
  obtain ⟨x, e⟩ := vreg_lo k hk
  rw [e]; simp only [qv, State.vy, State.ymm, hx, hy]

/-! ## The vector part of an iteration -/

/-- The loads under the mask (in `vreg R`), OR'ed into the accumulators. -/
def selVec (l : Lay) : List Instr :=
  [.eop (.vmovq (vreg l.R) .rax), .eop (.vpbroadcastq (vreg l.R) (vreg l.R))] ++
  ((List.range l.R).flatMap fun k => [.evLoad (vreg (l.R + 1)) (at_ .r8 (32 * k)),
    .eop (.bin .vpandq (vreg (l.R + 1)) (vreg (l.R + 1)) (vreg l.R)),
    .eop (.bin .vporq (vreg k) (vreg k) (vreg (l.R + 1)))])

def selLim (l : Lay) : Reg → Nat := fun b => if b = .r8 then l.NB else 0

def selTerm (k : Nat) : T := .or (.reg k) (.and (.ld .r8 (32 * k)) (.bc (.lane0 (.gpr .rax))))

def checkSel (l : Lay) : Bool :=
  match ESym.init.run (selLim l) (selVec l) with
  | some σ => (List.range l.R).all fun k => decide (σ.reg k = selTerm k)
  | none => false

theorem checkSel_ok (hl : LayOk l) : checkSel l = true := by
  rcases hl with rfl | rfl | rfl <;> decide +kernel

theorem selVec_ok (hl : LayOk l) {s : State} (hc : Ctx (selLim l) s) :
    WP isa (.block (selVec l)) s fun s' =>
      (∀ k < l.R, ∀ j < 4, qv s' (vreg k) j =
        qv s (vreg k) j ||| (s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (32 * k + 8 * j)) 64 &&& s.gpr .rax)) ∧
      Keeps s s' := by
  obtain ⟨_, hR10⟩ := hl.bounds
  have h := checkSel_ok hl
  unfold checkSel at h
  split at h
  · rename_i σ hσ
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    refine WP.mono (run_ok hc (SRel.init s) hσ) fun s' hs => ⟨fun k hk j hj => ?_,
      ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
    · rw [hs.reg _ j hj, vi_vreg k (by omega), h k hk]
      simp only [selTerm, T.eval, ite_true, AmmSym.G.eval]
  · cases h

/-! ## An iteration -/

theorem NB_lt (hl : LayOk l) : l.NB < 2 ^ 31 := by
  have := hl.D_bounds; omega

/-- The entry's end: the next entry, `ZF` after the last. -/
theorem selTail_ok (hl : LayOk l) {s : State} {base : Addr} {i : Nat} (hi : i < 16)
    (h8 : s.gpr .r8 = base + BitVec.ofNat 64 (l.NB * i)) (hc : s.gpr .rcx = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .add .r8 (.imm (BitVec.ofNat 32 l.NB)), .alu .add .rcx (.imm 1), .alu .cmp .rcx (.imm 16)])
      s fun s' =>
      s'.gpr .r8 = base + BitVec.ofNat 64 (l.NB * (i + 1)) ∧ s'.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧
      s'.zf = some (decide (i + 1 = 16)) ∧ Keep [.r8, .rcx] s s' ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr := by
  have sx := AmmSym.se_ofNat (NB_lt hl)
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8, .rcx] (Q := fun s' =>
    s'.gpr .r8 = base + BitVec.ofNat 64 (l.NB * (i + 1)) ∧ s'.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧
      s'.zf = some (decide (i + 1 = 16)) ∧ s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [h8, hc, sx, ofNat_add_one]
    and_intros
    any_goals rfl
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
    · rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_sub_beq (by omega) (by decide)]) rfl)
    fun s' ⟨⟨a, b, c, d, e, f, g⟩, k⟩ => ⟨a, b, c, k, d, e, f, g⟩

/-- After entries below `i` of the table at `base`, `v` the entry to read. -/
structure SelInv (l : Lay) (t₀ : State) (base : Addr) (v i : Nat) (t : State) : Prop where
  r8 : t.gpr .r8 = base + BitVec.ofNat 64 (l.NB * i)
  rcx : t.gpr .rcx = BitVec.ofNat 64 i
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → t.gpr r = t₀.gpr r
  mem : t.mem = t₀.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  mxcsr : t.mxcsr = t₀.mxcsr
  acc : ∀ k < l.R, ∀ j < 4, qv t (vreg k) j =
    if v < i then t₀.mem.readW (base + BitVec.ofNat 64 (l.NB * v + 32 * k + 8 * j)) 64 else 0

def selBody (l : Lay) : List Instr :=
  [.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .eop (.vmovq (vreg l.R) .rax), .eop (.vpbroadcastq (vreg l.R) (vreg l.R))] ++
  ((List.range l.R).flatMap fun k => [.evLoad (vreg (l.R + 1)) (at_ .r8 (32 * k)),
    .eop (.bin .vpandq (vreg (l.R + 1)) (vreg (l.R + 1)) (vreg l.R)),
    .eop (.bin .vporq (vreg k) (vreg k) (vreg (l.R + 1)))]) ++
  [.alu .add .r8 (.imm (BitVec.ofNat 32 l.NB)), .alu .add .rcx (.imm 1), .alu .cmp .rcx (.imm 16)]

/-- Entry `i`. -/
theorem selIter_ok (hl : LayOk l) {t₀ t : State} {base : Addr} {v i : Nat} (hv : v < 16) (hi : i < 16)
    (hd : t₀.gpr .rdx = BitVec.ofNat 64 v)
    (hin : ∀ i < 16, ∀ d n, 0 < n → d + n ≤ l.NB →
      InRegions (t₀.rd ++ t₀.wr) (base + BitVec.ofNat 64 (l.NB * i + d)) n)
    (h : SelInv l t₀ base v i t) :
    WP isa (.block (selBody l)) t fun t' => SelInv l t₀ base v (i + 1) t' ∧ t'.zf = some (decide (i + 1 = 16)) := by
  obtain ⟨_, hR10⟩ := hl.bounds
  rw [show selBody l = [.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1),
    .alu .sbb .rax (.reg .rax)] ++ (selVec l ++ [.alu .add .r8 (.imm (BitVec.ofNat 32 l.NB)), .alu .add .rcx (.imm 1),
      .alu .cmp .rcx (.imm 16)]) by simp only [selBody, selVec, List.cons_append, List.nil_append],
    WP.block_append_iff]
  have hdx : t.gpr .rdx = BitVec.ofNat 64 v := (h.gpr _ (by decide) (by decide) (by decide)).trans hd
  refine WP.mono (selMask_ok hi hv h.rcx hdx) fun t₁ ⟨m₁, k₁, me₁, x₁, y₁, mx₁⟩ => ?_
  have r8₁ : t₁.gpr .r8 = base + BitVec.ofNat 64 (l.NB * i) := by rw [k₁.gpr (by decide)]; exact h.r8
  have hc : Ctx (selLim l) t₁ := fun b d n hn hdn => by
    by_cases b8 : b = .r8
    · subst b8
      simp only [selLim, ite_true] at hdn
      rw [r8₁, k₁.2.1, k₁.2.2, h.rd, h.wr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hin i hi d n hn hdn
    · simp only [selLim, b8, ite_false] at hdn; omega
  rw [WP.block_append_iff]
  refine WP.mono (selVec_ok hl hc) fun t₂ ⟨v₂, k₂⟩ => ?_
  refine WP.mono (selTail_ok (base := base) hl hi (by rw [k₂.gpr _ (by decide)]; exact r8₁)
    (by rw [k₂.gpr _ (by decide), k₁.gpr (by decide)]; exact h.rcx))
    fun t₄ ⟨r8₄, rcx₄, z₄, k₄, me₄, x₄, y₄, mx₄⟩ => ⟨⟨r8₄, rcx₄, fun r r1 r2 r3 => ?_, ?_, ?_, ?_, ?_,
      fun k hk j hj => ?_⟩, z₄⟩
  · rw [k₄.gpr (by simp [r2, r3]), k₂.gpr _ r1, k₁.gpr (by simp [r1])]; exact h.gpr r r1 r2 r3
  · rw [me₄, k₂.mem, me₁, h.mem]
  · rw [k₄.2.1, k₂.rd, k₁.2.1, h.rd]
  · rw [k₄.2.2, k₂.wr, k₁.2.2, h.wr]
  · rw [mx₄, k₂.mxcsr, mx₁, h.mxcsr]
  · rw [qv_lo x₄ y₄ (by omega), v₂ k hk j hj, qv_lo x₁ y₁ (by omega), m₁, h.acc k hk j hj, me₁, h.mem, r8₁,
      selMask_and]
    by_cases hiv : i = v
    · subst hiv
      simp only [Nat.lt_irrefl, ite_false, decide_true, ite_true, Nat.lt_succ_self, zero_or64]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
    · simp only [hiv, decide_false, Bool.false_eq_true, ite_false, or_zero64]
      by_cases hlt : v < i
      · simp only [hlt, show v < i + 1 by omega, ite_true]
      · simp only [hlt, show ¬ v < i + 1 by omega, ite_false]

/-- The loop over the sixteen entries, from entry `16 - n`. -/
theorem selLoop_ok (hl : LayOk l) {t₀ : State} {base : Addr} {v : Nat} (hv : v < 16)
    (hd : t₀.gpr .rdx = BitVec.ofNat 64 v)
    (hin : ∀ i < 16, ∀ d n, 0 < n → d + n ≤ l.NB →
      InRegions (t₀.rd ++ t₀.wr) (base + BitVec.ofNat 64 (l.NB * i + d)) n) :
    ∀ n t, 1 ≤ n → n ≤ 16 → SelInv l t₀ base v (16 - n) t →
      WP isa (.loop (.block (selBody l)) .ne) t (SelInv l t₀ base v 16) := by
  intro n t h1 h16 hI
  refine WP.loop (M := isa) (body := .block (selBody l)) (c := .ne) (Q := SelInv l t₀ base v 16)
    (fun n t => 1 ≤ n ∧ n ≤ 16 ∧ SelInv l t₀ base v (16 - n) t) ?_ n t ⟨h1, h16, hI⟩
  intro n t ⟨h1, h16, hI⟩
  refine WP.mono (selIter_ok hl hv (by omega) hd hin hI) fun t' ⟨hI', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · exact .inl ⟨by simp, hI'⟩
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (16 - n + 1 = 16) by omega), Bool.not_false], n - 1,
      by omega, by omega, by omega, by rw [show 16 - (n - 1) = 16 - n + 1 by omega]; exact hI'⟩

/-! ## The whole selection -/

/-- The zeroing of the `R` accumulators. -/
def zerosR (l : Lay) : List Instr :=
  (List.range l.R).map fun k => .eop (.bin .vpxorq (vreg k) (vreg k) (vreg k))

def checkZerosR (l : Lay) : Bool :=
  match ESym.init.run (fun _ => 0) (zerosR l) with
  | some σ => (List.range l.R).all fun r => decide (σ.reg r = .zero)
  | none => false

theorem checkZerosR_ok (hl : LayOk l) : checkZerosR l = true := by
  rcases hl with rfl | rfl | rfl <;> decide +kernel

theorem zerosR_ok (hl : LayOk l) {s : State} :
    WP isa (.block (zerosR l)) s fun s' => (∀ r < l.R, ∀ t < 4, qv s' (vreg r) t = 0) ∧ Keeps s s' := by
  obtain ⟨_, hR10⟩ := hl.bounds
  have h := checkZerosR_ok hl
  unfold checkZerosR at h
  split at h
  · rename_i σ hσ
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    refine WP.mono (run_ok (fun b d n hn hd => absurd hd (by omega)) (SRel.init s) hσ) fun s' hs =>
      ⟨fun r hr t ht => ?_, ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
    rw [hs.reg _ t ht, vi_vreg r (by omega), h r hr]; rfl
  · cases h

/-- The nibble `select` reads: the top 4 bits of the quadword at `oV`. -/
def nib (l : Lay) (m : Mem) (B : Addr) (p : Nat) : Nat := (word m B (l.D * p + l.oV)).toNat / 2 ^ 60

theorem nib_lt (m : Mem) (B : Addr) (p : Nat) : nib l m B p < 16 := by
  unfold nib; have := (word m B (l.D * p + l.oV)).isLt; omega

theorem oV_bounds (hl : LayOk l) : l.oTab + 16 * l.NB ≤ l.oV ∧ l.oS + l.NB ≤ l.oTab ∧ l.oV + 8 ≤ l.D := by
  rcases hl with rfl | rfl | rfl <;> decide

/-- `[S] := T_v` for prime `p`. -/
theorem select_ok (hl : LayOk l) {s : State} {B : Addr} {p : Nat} (hp : p < 2) (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * l.D)) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (select l p)) s fun s' =>
      (∀ q < l.L, limb l s'.mem B (l.D * p + l.oS) q = limb l s.mem B (l.D * p + l.oTab + l.NB * nib l s.mem B p) q) ∧
      Outside B (l.D * p + l.oS) l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hR, hR10⟩ := hl.bounds
  have hD := hl.D_bounds
  obtain ⟨o1, o2, o3⟩ := oV_bounds hl
  have hn := hs.nowrap
  have hDp : l.D * p ≤ l.D := by rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> simp
  have rdS : ∀ d n, 0 < n → d + n ≤ 2 * l.D → InRegions (s.rd ++ s.wr) (off B d) n := fun d n hn hd =>
    let ⟨_, h, c⟩ := hs.region hd hn; ⟨_, List.mem_append_right _ h, c⟩
  let v := nib l s.mem B p
  have hv : v < 16 := nib_lt _ _ _
  let base := off B (l.D * p + l.oTab)
  refine WP.seq ?_
  rw [List.append_assoc]
  refine setOff (c := l.D * p + l.oTab) (by omega) fun s₁ u₁ => ?_
  rw [hB] at u₁
  change WP isa (.block (([.mov .rdx (.mem (at_ .rbx (l.D * p + l.oV))), .shift .shr .rdx 60,
    .mov32 .rcx (.imm 0)] : List Instr) ++ zerosR l)) s₁ _
  rw [WP.block_append_iff]
  have rbx₁ : s₁.gpr .rbx = B := by rw [u₁.other _ (by decide), hB]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 v ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧ t.xmm = s₁.xmm ∧ t.ymmHi = s₁.ymmHi ∧ t.mxcsr = s.mxcsr) (by
    have hld : InRegions (s₁.rd ++ s₁.wr) (B + BitVec.ofNat 64 (l.D * p + l.oV)) 8 := by
      rw [u₁.rd, u₁.wr]; exact rdS _ 8 (by decide) (by omega)
    xrun [ea_rG rbx₁, hld, u₁.mem, shr60]
    and_intros
    any_goals rfl
    · exact u₁.mxcsr) rfl) fun s₂ ⟨⟨dx₂, cx₂, me₂, x₂, y₂, mx₂⟩, k₂⟩ => ?_
  refine WP.mono (zerosR_ok hl) fun s₃ ⟨z₃, k₃⟩ => ?_
  have hin : ∀ i < 16, ∀ d n, 0 < n → d + n ≤ l.NB →
      InRegions (s₃.rd ++ s₃.wr) (base + BitVec.ofNat 64 (l.NB * i + d)) n := fun i hi d n hn hdn => by
    rw [k₃.rd, k₃.wr, k₂.2.1, k₂.2.2, u₁.rd, u₁.wr, off_add]
    have : l.NB * i + d + n ≤ l.NB * 16 := by
      have := Nat.mul_le_mul_left l.NB (show i ≤ 15 by omega); omega
    exact rdS _ n hn (by omega)
  have dx₃ : s₃.gpr .rdx = BitVec.ofNat 64 v := by rw [k₃.gpr _ (by decide)]; exact dx₂
  have i₀ : SelInv l s₃ base v (16 - 16) s₃ := ⟨by
      rw [k₃.gpr _ (by decide), k₂.gpr (by decide), u₁.self]; exact (BitVec.add_zero _).symm,
    by rw [k₃.gpr _ (by decide)]; exact cx₂, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl,
    fun k hk j hj => by rw [z₃ k hk j hj]; simp⟩
  refine WP.seq (WP.mono (selLoop_ok hl hv dx₃ hin 16 s₃ (by decide) (Nat.le_refl _) i₀) fun s₄ h₄ => ?_)
  let Ls : List (Nat × VReg) := (List.range l.R).map fun k => (l.D * p + l.oS + 32 * k, vreg k)
  have rbx₄ : s₄.gpr .rbx = B := by
    rw [h₄.gpr _ (by decide) (by decide) (by decide), k₃.gpr _ (by decide), k₂.gpr (by decide), rbx₁]
  have wr₄ : s₄.wr = s.wr := by rw [h₄.wr, k₃.wr, k₂.2.2, u₁.wr]
  have rd₄ : s₄.rd = s.rd := by rw [h₄.rd, k₃.rd, k₂.2.1, u₁.rd]
  have me₄ : s₄.mem = s.mem := by rw [h₄.mem, k₃.mem, me₂]
  rw [show ((List.range l.R).map fun k => Instr.evStore (at_ .rbx (l.D * p + l.oS + 32 * k)) (vreg k)) =
    storeCode .rbx Ls by simp only [storeCode, Ls, List.map_map, Function.comp_def]]
  have hL : ∀ x ∈ Ls, l.D * p + l.oS ≤ x.1 ∧ x.1 + 32 ≤ l.D * p + l.oS + l.NB := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hk; dsimp only; simp only [Lay.NB]; omega
  refine WP.mono (stores_gen Ls s₄ rbx₄ fun x hx => by
    have := hL x hx
    rw [wr₄]; exact let ⟨_, h, c⟩ := hs.region (d := x.1) (n := 32) (by omega) (by decide);
      ⟨_, h, c⟩) fun s' hs' => ?_
  subst hs'
  refine ⟨fun q hq => ?_, ?_, fun r r1 r2 r3 r4 => ?_, rd₄, wr₄, ?_⟩
  · have hk : q % l.R < l.R := Nat.mod_lt _ (by omega)
    have ht : q / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
    have e := word_wrList_unique B (e := l.D * p + l.oS + 32 * (q % l.R)) (t := q / l.R)
      (v := s₄.vy (vreg (q % l.R))) ht (by simp only [Lay.NB] at *; omega)
      (Ls.map fun x => (x.1, s₄.vy x.2)) s₄.mem
      (List.mem_map.2 ⟨(l.D * p + l.oS + 32 * (q % l.R), vreg (q % l.R)),
        List.mem_map.2 ⟨q % l.R, List.mem_range.2 hk, rfl⟩, rfl⟩)
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hy
        rw [List.mem_range] at hk'; dsimp only; simp only [Lay.NB] at *; omega)
      (fun x hx he => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hy
        rw [List.mem_range] at hk'; dsimp only at he ⊢
        rw [show k = q % l.R by omega])
    have qq := h₄.acc (q % l.R) hk (q / l.R) ht
    simp only [hv, ite_true] at qq
    show (word (wrList s₄.mem B _) B (l.D * p + l.oS + l.off q)).toNat = _
    rw [show l.D * p + l.oS + l.off q = l.D * p + l.oS + 32 * (q % l.R) + 8 * (q / l.R) by
      unfold Lay.off; omega, e]
    refine congrArg BitVec.toNat (qq.trans ?_)
    rw [k₃.mem, me₂, off_add]
    exact congrArg (fun d => s.mem.readW (off B d) 64) (by unfold Lay.off; dsimp only [v]; omega)
  · have o := wrList_outside' B (o := l.D * p + l.oS) (n := l.NB) (by omega)
      (Ls.map fun x => (x.1, s₄.vy x.2)) s₄.mem fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hL y hy
    exact fun x hx => (o x hx).trans (congrFun me₄ x)
  · show s₄.gpr r = _
    rw [h₄.gpr _ r1 r2 r4, k₃.gpr _ r1, k₂.gpr (by simp [r2, r3]), u₁.other _ r4]
  · show s₄.mxcsr = _
    rw [h₄.mxcsr, k₃.mxcsr, mx₂]

end VG.Proof.Bignum.X86_64.G
