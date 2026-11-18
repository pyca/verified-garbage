module

import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.MlKem.X86.TopSeq
import VerifiedGarbage.Proof.MlKem.X86.TopCall
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Base
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
public import VerifiedGarbage.Proof.Sha256.X86.Lit
public import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Params
public import VerifiedGarbage.Proof.MlKem.X86.TopKeep
import VerifiedGarbage.Proof.MlKem.X86.Table

/-! ### `MlDsa.X86.Sign.Inv`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on x86 (32-bit): what the pieces keep

The slots of polynomials (`nS` of them, `slot_ok`), families of consecutive
slots (`Fam`), and what a piece that writes the buffers `bs` keeps: the frame
of each call is widened to a few large buffers (`frIn`), so that what a whole
phase keeps is shown once (`Fam.keep`, `keepB`, `keepW'`). The tactic `ofs`
proves the arithmetic of offsets from the facts of `PS p`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlKem.X86 (sub_of_contains contains_at)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The slot of `Â[0, 0]`. -/
abbrev aBase (p : Params) : Nat := 5 + 4 * p.k + 3 * p.ℓ

/-- The number of slots of polynomials. -/
abbrev nS (p : Params) : Nat := 5 + 4 * p.k + 3 * p.ℓ + p.k * p.ℓ

variable {p : Params}

/-! ## Buffers within buffers -/

/-- `c` lies within `d`. -/
def In (c d : Buf) : Prop := c.arg = d.arg ∧ d.off ≤ c.off ∧ c.off + c.len ≤ d.off + d.len

theorem rgn_sub {Y : Lay} {s₀ : State} (hp : TPre Y s₀) {c d : Buf} (hc : Y.ok c = true) (hd : Y.ok d = true)
    (h : In c d) : Region.Sub (c.rgn s₀) (d.rgn s₀) := by
  obtain ⟨e, h₁, h₂⟩ := h
  show Region.Sub ⟨c.addr s₀, c.len⟩ ⟨d.addr s₀, d.len⟩
  have ea : c.addr s₀ = (d.ptr s₀).setWidth 64 + BitVec.ofNat 64 (c.off - d.off) := by
    show c.addr s₀ = d.addr s₀ + _
    rw [Buf.addr_eq hp hc, Buf.addr_eq hp hd, BitVec.add_assoc, ← BitVec.ofNat_add, e,
      show d.off + (c.off - d.off) = c.off by omega_using [h₁]]
  rw [ea]
  exact sub_of_contains (contains_at (by omega_using [h₁, h₂]) (Buf.fit hp hd))

/-- The frame of a piece, widened to the buffers `ds`. -/
theorem frIn {s₀ : State} (hp : TPre (Y p) s₀) {bs ds : List Buf} {N M : Nat} (hNM : N ≤ M) (hM : M ≤ 80)
    (h : ∀ c ∈ bs, (Y p).ok c = true ∧ ∃ d ∈ ds, (Y p).ok d = true ∧ In c d) {m m' : Mem}
    (fr : Frame (FR s₀ bs N) m m') : Frame (FR s₀ ds M) m m' :=
  fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hc', d, hd, hd', i⟩ := h c hc
      exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hd), rgn_sub hp hc' hd' i⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        stk_sub hp hNM (by show M + 16 ≤ 96; omega_using [hM])⟩

/-! ## Families of slots -/

/-- The `n` slots from `b` hold `f 0, …, f (n - 1)`. -/
def Fam (s₀ : State) (m : Mem) (b n : Nat) (f : Nat → Poly) : Prop :=
  ∀ j < n, PolyIs m (Buf.addr s₀ (pS (b + j))) (f j)

theorem Fam.congr {s₀ : State} {m : Mem} {b n : Nat} {f g : Nat → Poly} (h : Fam s₀ m b n f)
    (e : ∀ j < n, f j = g j) : Fam s₀ m b n g := fun j hj => e j hj ▸ h j hj

/-- A buffer of `scratch` apart from `[lo, hi)`, or not in `scratch`. -/
def Out (p : Params) (lo hi : Nat) (c : Buf) : Prop :=
  (Y p).ok c = true ∧ (c.arg = SC → c.off + c.len ≤ lo ∨ hi ≤ c.off)

/-- The slots of `y`, `ŷ` and `w`. -/
abbrev yB (p : Params) : Nat := 5 + p.k
abbrev yhB (p : Params) : Nat := 5 + p.k + p.ℓ
abbrev wB (p : Params) : Nat := 5 + p.k + 2 * p.ℓ

/-- The slots of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
abbrev s1B (p : Params) : Nat := 5 + 2 * p.k + 2 * p.ℓ
abbrev s2B (p : Params) : Nat := 5 + 2 * p.k + 3 * p.ℓ
abbrev t0B (p : Params) : Nat := 5 + 3 * p.k + 3 * p.ℓ

/-- A write apart from all of the families. -/
def OutK (p : Params) (n1 n2 n0 : Nat) (c : Buf) : Prop :=
  Out p (oP (aBase p)) (oP (nS p)) c ∧ Out p (oP (s1B p)) (oP (s1B p + n1)) c ∧
    Out p (oP (s2B p)) (oP (s2B p + n2)) c ∧ Out p (oP (t0B p)) (oP (t0B p + n0)) c

/-- A write apart from the first `n1`, `n2` and `n0` polynomials of `ŝ₁`,
`ŝ₂` and `t̂₀`. -/
def OutS (p : Params) (n1 n2 n0 : Nat) (c : Buf) : Prop :=
  Out p (oP (s1B p)) (oP (s1B p + n1)) c ∧ Out p (oP (s2B p)) (oP (s2B p + n2)) c ∧
    Out p (oP (t0B p)) (oP (t0B p + n0)) c

/-- A write that an iteration of the loop may do: apart from `Â`, `ŝ₁`,
`ŝ₂`, `t̂₀`, `CNT`, `KAP` and `ρ″`. -/
def OutI (p : Params) (c : Buf) : Prop :=
  OutK p p.ℓ p.k p.k c ∧ Out p oCNT (oKAP + 4) c ∧ Out p oMS (oMS + 64) c

/-- A write that the checks of an iteration may do, with `nh` polynomials of
the hint made: apart from what `OutI` keeps, `ĉ`, `c̃`, `y`, `w`, the hint,
`OK` and `ONES`. -/
def OutC (p : Params) (nh : Nat) (c : Buf) : Prop :=
  OutI p c ∧ Out p (oP 0) (oP 1) c ∧ Out p oCT (oCT + 64) c ∧ Out p (oP (yB p)) (oP (wB p + p.k)) c ∧
    Out p (oP 5) (oP (5 + nh)) c ∧ Out p oOK (oOK + 4) c ∧ Out p oONES (oONES + 4) c

theorem PS.w1pos {p : Params} (ps : PS p) : 0 < p.k * w1Len p :=
  Nat.mul_pos (by have := ps.hk; omega_using [this]) (by rcases ps.hw1Len with h | h <;> omega_using [h])

/-- The facts of `PS p` that the offsets need, in the context. -/
tactic_template "ofs" : tactic => `(tactic| (
  have _ := (ps).hk; have _ := (ps).hl; have _ := (ps).hscr; have _ := (ps).hsigLen; have _ := (ps).hskLen
  have _ := (ps).hcLen; have _ := (ps).hzLen; have _ := (ps).hw1; have _ := (ps).hω; have _ := PS.w1pos ps
  try simp only [nS, aBase, s1B, s2B, t0B, yB, yhB, wB] at *
  set_option linter.unusedSimpArgs false in
  simp only [Lay.apart, Lay.okW_iff, Lay.ok_iff, Lay.sep_iff, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
    true_and, ne_eq, not_true_eq_false, false_and, or_false, true_or, or_true, Out, In,
    Y_n, Y_alen0, Y_alen1, Y_alen2, Y_alen3, Y_alen4, Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4,
    oP, SC, oPS, oRS, oHIN, oMS, oCT, oW1, oST, oWK, oOK, oCNT, oKAP, oONES, skS1, skS2, skT0, sigZ, sigH, aBase, s1B, s2B, t0B, OutK, OutS, OutI, OutC, oKEYS, yB, yhB, wB, bMu, bRnd, bSk, bSig]
  omega_arith))

/-- A check of offsets that mentions no variable but the parameter set and
bounded indices, decided for each parameter set (`decide_at`): cheaper than
`ofs`, which unfolds it into arithmetic on the parameters for `omega`, unless
there are many indices to try. Each conjunct is decided on its own. -/
tactic_template "ofsd" : tactic => `(tactic| (
  try dsimp only [VG.Proof.MlDsa.X86.Sign.Out, VG.Proof.MlDsa.X86.Sign.In, VG.Proof.MlDsa.X86.Sign.OutK, VG.Proof.MlDsa.X86.Sign.OutS,
    VG.Proof.MlDsa.X86.Sign.OutI, VG.Proof.MlDsa.X86.Sign.OutC]
  try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, true_implies]
  have hmem := (‹VG.Proof.MlDsa.X86.Sign.PS _›).mem
  and_intros
  all_goals decide_at hmem))

/-! ## Slots -/

section
variable (ps : PS p)
include ps

theorem slot_ok {j : Nat} (hj : j < nS p) : (Y p).okW (pS j) = true := by ofs
theorem slot_ok' {j : Nat} (hj : j < nS p) : (Y p).ok (pS j) = true := (Lay.okW_iff.mp (slot_ok ps hj)).1

omit ps in
/-- An entry of `Â` is a slot. -/
theorem aP_eq {i j : Nat} : aP p i j = pS (5 + 4 * p.k + 3 * p.ℓ + (p.ℓ * i + j)) := by
  simp only [aP, Nat.add_assoc]

omit ps in
theorem aIdx {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have : p.ℓ * i + p.ℓ ≤ p.ℓ * p.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [Nat.mul_comm p.k]; omega_using [hj, this]

end

theorem apart_of {b : Buf} (hb : (Y p).ok b = true) (hbs : b.arg = SC) {bs : List Buf}
    (h : ∀ c ∈ bs, Out p b.off (b.off + b.len) c) : (Y p).apart b bs = true := by
  simp only [Lay.apart, hb, Bool.true_and, List.all_eq_true, Bool.and_eq_true]
  intro c hc
  obtain ⟨hc₁, hc₂⟩ := h c hc
  refine ⟨hc₁, Lay.sep_iff.mpr ?_⟩
  by_cases e : b.arg = c.arg
  · exact .inl ⟨e, (hc₂ (e ▸ hbs)).symm⟩
  · exact .inr ⟨e, .inl (by rw [hbs]; rfl)⟩

theorem Fam.keep {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {b n : Nat} (hb : b + n ≤ nS p)
    (h : ∀ c ∈ bs, Out p (oP b) (oP (b + n)) c) {f : Nat → Poly} (hf : Fam s₀ m b n f) : Fam s₀ m' b n f :=
  fun j hj => polyIs_congr (VG.Proof.MlKem.X86.Top.keep hp (N := N) (by show N + 16 ≤ 96; omega_using [hN])
    (apart_of (slot_ok' ps (Nat.lt_of_lt_of_le (by omega_using [hj] : b + j < b + n) hb)) rfl fun c hc => by
      obtain ⟨h₁, h₂⟩ := h c hc
      exact ⟨h₁, fun e => by simp only [oP] at h₂ ⊢; have := h₂ e; omega_using [hj, this]⟩) fr) (hf j hj)

theorem keepB {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {o l : Nat} (hc : (Y p).ok (sc o l) = true)
    (h : ∀ c ∈ bs, Out p o (o + l) c) : bytesAt m' (Buf.addr s₀ (sc o l)) l = bytesAt m (Buf.addr s₀ (sc o l)) l :=
  keepBytes hp (N := N) (by show N + 16 ≤ 96; omega_using [hN]) (apart_of hc rfl h) fr

theorem keepW' {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {o : Nat} (hc : (Y p).ok (sc o 4) = true)
    (h : ∀ c ∈ bs, Out p o (o + 4) c) : m'.readW (Buf.addr s₀ (sc o 4)) 32 = m.readW (Buf.addr s₀ (sc o 4)) 32 :=
  keepW hp (N := N) (by show N + 16 ≤ 96; omega_using [hN]) (apart_of hc rfl h) fr

theorem keepP {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {j : Nat} (hj : j < nS p)
    (h : ∀ c ∈ bs, Out p (oP j) (oP (j + 1)) c) {f : Poly} (hf : PolyIs m (Buf.addr s₀ (pS j)) f) :
    PolyIs m' (Buf.addr s₀ (pS j)) f := by
  have := Fam.keep hp ps hN fr (b := j) (n := 1) (by omega_using [hj]) h (f := fun _ => f) fun i hi => by
    rw [show i = 0 by omega_using [hi]]; exact hf
  exact this 0 (by decide)

/-- The first `r` slots of a family, and the rest. -/
theorem Fam.snoc {s₀ : State} {m : Mem} {b n : Nat} {f : Nat → Poly} (h : Fam s₀ m b n f)
    (h' : PolyIs m (Buf.addr s₀ (pS (b + n))) (f n)) : Fam s₀ m b (n + 1) f := fun j hj => by
  by_cases e : j < n
  · exact h j e
  · rw [show j = n by omega_using [hj, e]]; exact h'

end VG.Proof.MlDsa.X86.Sign

end

end

/-! ### `MlDsa.X86.Sign.Blocks`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on x86 (32-bit): the blocks between calls

Loads and stores of words and bytes of `scratch` from `Ctx` (`wp_ldsc`,
`wp_stsc`, `wp_st8sc`), and the pieces made of them: sequences (`seqR_piece`),
the empty block (`nil_piece`), and the branch on `OK` (`okIte_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {A B : State → State → Prop}

/-- The word of `scratch` at `o`. -/
abbrev scw (s₀ s : State) (o : Nat) : BitVec 32 := s.mem.readW (Buf.addr s₀ (sc o 4)) 32

theorem ea_sc {s₀ s : State} (h : Ctx (Y p) s₀ s) (o : Nat) (n : Nat) :
    s.ea (at_ .esi o) = Buf.addr s₀ (sc o n) := by
  simp only [State.ea, at_]; rw [h.esi]; rfl

/-- `r ← ` the word of `scratch` at `o`. -/
theorem wp_ldsc {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o : Nat} (hc : (Y p).ok (sc o 4) = true)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [r] s s' → s'.gpr r = scw s₀ s o → WP isa (.block is) s' Q) :
    WP isa (.block (.mov r (.mem (at_ .esi o)) :: is)) s Q := by
  have hin : InRegions (s.rd ++ s.wr) (Buf.addr s₀ (sc o 4)) 4 := by
    have := Buf.inRegR hp hc h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  exact wp_movm' (by rw [ea_sc h o 4]; exact hin) fun s' o' v' => k s' o' (by rw [v', ea_sc h o 4])

theorem ctx_write {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o n w : Nat} (hc : (Y p).okW (sc o n) = true)
    (hw : w / 8 ≤ n) (v : BitVec w) : Ctx (Y p) s₀ { s with mem := s.mem.writeW (Buf.addr s₀ (sc o n)) v } := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := w / 8) (by show 0 + w / 8 ≤ n; omega_using [hw])
  rw [BitVec.add_zero] at hcr
  exact ⟨h.esp, h.rd, h.wr, h.esi, h.frame.writeW hr _ hcr⟩

/-- The word of `scratch` at `o` ← `r`. -/
theorem wp_stsc {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o : Nat} (hc : (Y p).okW (sc o 4) = true)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → (∀ x, s'.gpr x = s.gpr x) → s'.mem = s.mem.writeW (Buf.addr s₀ (sc o 4)) (s.gpr r) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ .esi o) r :: is)) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  have hin : InRegions s.wr (Buf.addr s₀ (sc o 4)) 4 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  refine wp_store' (by rw [ea_sc h o 4]; exact hin) fun s' g' r' w' m' => ?_
  rw [ea_sc h o 4] at m'
  have c := ctx_write hp h hc (w := 32) (by decide) (s.gpr r)
  exact k s' ⟨by rw [g']; exact c.esp, by rw [r']; exact c.rd, by rw [w']; exact c.wr, by rw [g']; exact c.esi,
    by rw [m']; exact c.frame⟩ g' m'

/-- The byte of `scratch` at `o` ← the low byte of `r`. -/
theorem wp_st8sc {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o : Nat} (hc : (Y p).okW (sc o 1) = true)
    {r : Reg8} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → (∀ x, s'.gpr x = s.gpr x) →
      s'.mem = s.mem.writeW (Buf.addr s₀ (sc o 1)) ((s.gpr r.reg).setWidth 8) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 (at_ .esi o) r :: is)) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  have hin : InRegions s.wr (Buf.addr s₀ (sc o 1)) 1 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 1) (Nat.le_refl _)
    simpa using this
  refine wp_store8 (by rw [ea_sc h o 1]; exact hin) ?_
  rw [ea_sc h o 1]
  exact k _ (ctx_write hp h hc (w := 8) (by decide) _) (fun _ => rfl) rfl

theorem wp_addr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d + s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d + s.gpr r) (decide (2 ^ 32 ≤ (s.gpr d).toNat + (s.gpr r).toNat))
      (addOverflow (s.gpr d) (s.gpr r) (s.gpr d + s.gpr r))).setReg d (s.gpr d + s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_test {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [] s s' → s'.zf = some (s.gpr r &&& s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test r (.reg r) :: is)) s Q :=
  wp_cons (s' := arithFlags s (s.gpr r &&& s.gpr r) false false)
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_subi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - v → s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat))
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]) rfl)

/-! ## Pieces -/

/-- The empty block. -/
theorem nil_piece (h : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → B s₀ s) : SP p A B (.block []) where
  wp s₀ s hp ha := WP.block_nil_iff.mpr (h s₀ s hp ha)
  ct _ _ _ _ _ := fun _ _ _ _ _ _ _ e₁ e₂ => by
    rw [Exec.block_iff] at e₁ e₂
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    exact ⟨e₁.2.symm.trans e₂.2, trivial⟩

/-- `f a, …, f (a + n - 1)`, from pieces for each. -/
theorem seqR_piece {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (a n : Nat), (∀ i, a ≤ i → i < a + n → SP p (I i) (I (i + 1)) (f i)) → SP p (I a) (I (a + n)) (seqR f a n)
  | a, 0, _ => nil_piece fun _ _ _ h => h
  | a, n + 1, h => by
    refine Piece.seq (h a (Nat.le_refl _) (by omega_using [])) ?_
    have := seqR_piece (I := I) (a + 1) n fun i hi hi' => h i (by omega_using [hi]) (by omega_using [hi'])
    rwa [show a + 1 + n = a + (n + 1) by omega_using []] at this

/-- The branch on `OK`, which is 1 or 0 as `b` of the initial state says. -/
theorem okIte_piece (hc : (Y p).ok (sc oOK 4) = true) {t e : Prog isa} (b : State → Bool)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ scw s₀ s oOK = if b s₀ then 1 else 0)
    (hb : ∀ s₀ s₀', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → b s₀ = b s₀')
    (ht : SP p (fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧ b s₀ = true) B t)
    (he : SP p (fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧ b s₀ = false) B e) :
    SP p A B (ifOkElse t e) := by
  refine Piece.seq (B := fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧
    s₁.zf = some (!b s₀)) (blk_piece (fun s₀ s hp ha => (hA s₀ s hp ha).1) (fun s₀ s hp ha => ?_) rfl) ?_
  · obtain ⟨h, hok⟩ := hA s₀ s hp ha
    refine wp_ldsc hp h hc fun s₁ o₁ v₁ => wp_test fun s₂ o₂ z₂ => WP.block_nil_iff.mpr ?_
    have o := o₁.trans o₂
    refine ⟨⟨s, ha, h.only o (by simp) (by simp), o.mem⟩, ?_⟩
    rw [z₂, v₁, hok]
    cases b s₀ <;> rfl
  · refine Piece.ite b (fun s₀ s₁ hp ha => ?_) hb (ht.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
      (he.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
    show s₁.zf.map (!·) = _
    rw [ha.2]; cases b s₀ <;> rfl

end VG.Proof.MlDsa.X86.Sign

end

end

/-!
# ML-DSA signing on x86 (32-bit): words and bytes of `scratch`

The small blocks between calls, as what they leave in `scratch` and the frame
of what they change: a word or a byte set (`wp_st32`, `wp_st8`), `OK ← OK ∧
eax` (`wp_andOK`) and `ONES ← ONES + eax` (`wp_addOnes`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

theorem sc_ok (ps : PS p) {o n : Nat} (h : o + n ≤ 5120) (hn : 0 < n) : (Y p).okW (sc o n) = true := by ofs

theorem sc_ok' (ps : PS p) {o n : Nat} (h : o + n ≤ 5120) (hn : 0 < n) : (Y p).ok (sc o n) = true :=
  (Lay.okW_iff.mp (sc_ok ps h hn)).1

/-- The address of a part of a buffer. -/
theorem addr_off {Y : Lay} {s₀ : State} (hp : TPre Y s₀) {a o d l l' : Nat} (h₁ : Y.ok ⟨a, o, l⟩ = true)
    (h₂ : Y.ok ⟨a, o + d, l'⟩ = true) : Buf.addr s₀ ⟨a, o + d, l'⟩ = Buf.addr s₀ ⟨a, o, l⟩ + BitVec.ofNat 64 d := by
  rw [Buf.addr_eq hp h₂, Buf.addr_eq hp h₁, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bytes1_write (m : Mem) (a : Addr) (v : Byte) : bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
    VG.Proof.MlKem.writeW8_apply, ite_true]

theorem setWidth8_ofNat (v : Nat) : (BitVec.ofNat 32 v).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd v (by decide)

theorem and01 (a b : Bool) :
    ((if a then 1 else 0 : BitVec 32) &&& (if b then 1 else 0)) = if a && b then 1 else 0 := by
  cases a <;> cases b <;> rfl

section
variable {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s)
include hp h

/-- The word at `o` set to `v`. -/
theorem wp_st32 {o : Nat} (hc : (Y p).okW (sc o 4) = true) (v : Nat) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc o 4] 0) s.mem s'.mem → scw s₀ s' o = BitVec.ofNat 32 v →
      WP isa (.block is) s' Q) :
    WP isa (.block (st32 o v ++ is)) s Q := by
  simp only [st32, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ o₁ v₁ => ?_
  refine wp_stsc hp (h.only o₁ (by simp) (by simp)) hc fun s₂ c₂ g₂ m₂ => k s₂ c₂ ?_ ?_
  · rw [m₂, o₁.mem]; exact frW32 (Y := Y p)
  · rw [scw, m₂, Mem.readW_writeW_self32, v₁]

/-- The byte at `o` set to `v`. -/
theorem wp_st8 {o : Nat} (hc : (Y p).okW (sc o 1) = true) (v : Nat) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc o 1] 0) s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ (sc o 1)) 1 = [BitVec.ofNat 8 v] → WP isa (.block is) s' Q) :
    WP isa (.block (st8 o v ++ is)) s Q := by
  simp only [st8, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ o₁ v₁ => ?_
  refine wp_st8sc hp (h.only o₁ (by simp) (by simp)) hc fun s₂ c₂ g₂ m₂ => k s₂ c₂ ?_ ?_
  · rw [m₂, o₁.mem]; exact frW8 (Y := Y p)
  · rw [m₂, bytes1_write]; show [(s₁.gpr .eax).setWidth 8] = _; rw [v₁, setWidth8_ofNat]

/-- `OK ← OK ∧ eax`. -/
theorem wp_andOK (ps : PS p) {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc oOK 4] 0) s.mem s'.mem →
      scw s₀ s' oOK = scw s₀ s oOK &&& s.gpr .eax → Q s') :
    WP isa (.block andOK) s Q := by
  unfold andOK
  refine wp_ldsc hp h (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_andr fun s₂ o₂ v₂ => ?_
  have o := o₁.trans o₂
  refine wp_stsc hp (h.only o (by simp) (by simp)) (sc_ok ps (by decide) (by decide)) fun s₃ c₃ g₃ m₃ =>
    WP.block_nil_iff.mpr (k s₃ c₃ ?_ ?_)
  · rw [m₃, o.mem]; exact frW32 (Y := Y p)
  · rw [scw, m₃, Mem.readW_writeW_self32, v₂, v₁, o₁.gpr .eax (by simp)]

/-- `ONES ← ONES + eax`. -/
theorem wp_addOnes (ps : PS p) {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc oONES 4] 0) s.mem s'.mem →
      scw s₀ s' oONES = scw s₀ s oONES + s.gpr .eax → Q s') :
    WP isa (.block addOnes) s Q := by
  unfold addOnes
  refine wp_ldsc hp h (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_addr fun s₂ o₂ v₂ => ?_
  have o := o₁.trans o₂
  refine wp_stsc hp (h.only o (by simp) (by simp)) (sc_ok ps (by decide) (by decide)) fun s₃ c₃ g₃ m₃ =>
    WP.block_nil_iff.mpr (k s₃ c₃ ?_ ?_)
  · rw [m₃, o.mem]; exact frW32 (Y := Y p)
  · rw [scw, m₃, Mem.readW_writeW_self32, v₂, v₁, o₁.gpr .eax (by simp)]

end

/-! ## Frames of the small blocks -/

theorem fr0 {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80) {m m' : Mem}
    (fr : Frame (FR s₀ bs 0) m m') : Frame (FR s₀ bs N) m m' :=
  fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        stk_sub hp (Nat.zero_le N) (by show N + 16 ≤ 96; omega_using [hN])⟩

theorem scr_ge (ps : PS p) : oP (nS p) ≤ scrLen p := by ofsd

/-- The frame of a piece that writes only in `scratch[lo : hi]`, as that buffer. -/
theorem frSc {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N M : Nat} (hNM : N ≤ M) (hM : M ≤ 80)
    {lo hi : Nat} (hlh : lo < hi) (hhi : hi ≤ scrLen p)
    (h : ∀ c ∈ bs, c.arg = SC ∧ lo ≤ c.off ∧ c.off + c.len ≤ hi ∧ 0 < c.len) {m m' : Mem}
    (fr : Frame (FR s₀ bs N) m m') : Frame (FR s₀ [sc lo (hi - lo)] M) m m' :=
  frIn hp hNM hM (fun c hc => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h c hc
    refine ⟨Lay.ok_iff.mpr ⟨by rw [h₁, Y_n]; decide, h₄, by rw [h₁, Y_alen4]; omega_using [hhi, h₃]⟩, _, List.mem_singleton_self _,
      Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 4 < 5), by simp only; omega_using [hlh], by rw [Y_alen4]; simp only; omega_using [hlh, hhi]⟩, h₁, by simp only; omega_using [h₂],
      by simp only; omega_using [h₃]⟩) fr

/-- `keepB`, for bytes of `scratch` that may be none. -/
theorem keepB0 {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {o l : Nat} (L : Nat) (hl : o + l ≤ scrLen p)
    (h : ∀ c ∈ bs, Out p o (o + l) c) : bytesAt m' (Buf.addr s₀ (sc o L)) l = bytesAt m (Buf.addr s₀ (sc o L)) l := by
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rfl
  · exact keepB hp hN fr (l := l) (Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 4 < 5), hl0, by rw [Y_alen4]; exact hl⟩) h

end VG.Proof.MlDsa.X86.Sign
