module
-- separate module: the five-limb field's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.X25519.PPC64LE.Fe51.Core
public import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on PPC64LE, five 51-bit limbs: the field operations

Each operation of `Impl/X25519/PPC64LE/Fe51.lean` takes its operands' limbs
from the working space into `ra` and `rb` (`limbs_ok`, a loop over the limbs,
with a step for each kind of operand: `ldV_ok`, `ldAdd_ok`, `ldSub_ok`,
`ldSel_ok`, `a24Steps_ok`), then is `mulCore` or `sqrCore`. Each stores a
reduced element (`Tight`) whose residue (`FS`) is the operation of
`Spec/X25519.lean` on its operands'.
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE.Fe51

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE.Fe51
open VG.Spec.X25519 (P Fe a24)
open VG.Proof.X25519 (toFe)

/-- The element at `o`. -/
def FS (m : Mem) (B : Addr) (o : Nat) : Fe := toFe (V5 m B o)

/-- `lo` holds the element at `o`. -/
def LoOk (b : Addr) (o : Nat) (s : State) : Prop := ∀ k < 5, (s.gpr (lo k)).toNat = lw s.mem b o k

/-- Limb `k` of `2p`. -/
def twoPv (k : Nat) : Nat := if k = 0 then 2 ^ 52 - 38 else 2 ^ 52 - 2

theorem val5_add (f g : Nat → Nat) : val5 (fun k => f k + g k) = val5 f + val5 g := by
  simp only [val5]; omega_using []

theorem val5_sub {a c d : Nat → Nat} (h : ∀ k < 5, d k + c k = a k + twoPv k) :
    val5 d + val5 c = val5 a + P * 2 :=
  sub_val (h 0 (by decide)) fun k hk hk5 => by
    have := h k hk5
    rw [twoPv, ite_eq_right (by omega_using [hk])] at this
    exact this

theorem toFe_dif {d a c : Nat} (h : d + c = a + P * 2) : toFe d = toFe a - toFe c :=
  VG.Proof.X25519.toFe_sub (by rw [h, Nat.add_mul_mod_self_left])

section
variable {b : Addr}

/-! ## Loops over the limbs -/

/-- A loop over the five limbs whose step `k` leaves `val k` in `rs k` and
`val' k` in `rs' k`, and writes otherwise only `tmp`. -/
theorem limbs_ok {f : Nat → List Instr} {rs rs' : Nat → Reg} {tmp ws : List Reg} {val val' : Nat → Nat}
    {s : State}
    (hws : ∀ k < 5, ∀ r ∈ rs k :: rs' k :: tmp, r ∈ ws)
    (hd : ∀ j < 5, ∀ k < 5, j < k → rs j ∉ rs k :: rs' k :: tmp ∧ rs' j ∉ rs k :: rs' k :: tmp)
    (hstep : ∀ k < 5, ∀ t, Rest ws s t → t.mem = s.mem →
      WP isa (.block (f k)) t fun t' => (t'.gpr (rs k)).toNat = val k ∧ (t'.gpr (rs' k)).toNat = val' k ∧
        Rest (rs k :: rs' k :: tmp) t t' ∧ t'.mem = t.mem) :
    WP isa (.block ((List.range 5).flatMap f)) s fun s' =>
      (∀ k < 5, (s'.gpr (rs k)).toNat = val k ∧ (s'.gpr (rs' k)).toNat = val' k) ∧ Rest ws s s' ∧
      s'.mem = s.mem := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun n t => Rest ws s t ∧ t.mem = s.mem ∧
    ∀ k < n, (t.gpr (rs k)).toNat = val k ∧ (t.gpr (rs' k)).toNat = val' k) (fun k t hk ⟨hr, hm, hv⟩ => ?_)
    5 (Nat.le_refl _) s ⟨Rest.refl _ _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s' ⟨hr, hm, hv⟩ => ⟨hv, hr, hm⟩
  refine WP.mono (hstep k hk t hr hm) fun t' ⟨v1, v2, r', m'⟩ =>
    ⟨hr.trans (r'.mono (hws k hk)), m'.trans hm, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j k with h | h
  · rw [r'.gpr _ (hd j (by omega_using [h, hk]) k hk h).1, r'.gpr _ (hd j (by omega_using [h, hk]) k hk h).2]
    exact hv j h
  · rw [show j = k by omega_using [h, hj]]; exact ⟨v1, v2⟩

/-- The registers of the five limbs. -/
abbrev regs5 (rs : Nat → Reg) : List Reg := [rs 0, rs 1, rs 2, rs 3, rs 4]

theorem ldV_eq (rs : Nat → Reg) (a : Nat) :
    ldV rs a = (List.range 5).flatMap fun k => [.load .d (rs k) .r6 (a + 8 * k)] := rfl

/-- The registers of an operand: five that differ, none `r6` or a temporary. -/
def OpRegs (rs : Nat → Reg) : Prop :=
  (∀ j < 5, ∀ k < 5, j < k → rs j ≠ rs k) ∧
  ∀ k < 5, rs k ∈ regs5 rs ∧ rs k ≠ .r6 ∧ rs k ≠ .r8 ∧ rs k ≠ .r9 ∧ rs k ≠ .r5 ∧ rs k ≠ .r4 ∧ rs k ≠ .r7 ∧
    rs k ≠ .r10

theorem opRegs_ra : OpRegs ra := by unfold OpRegs; decide
theorem opRegs_rb : OpRegs rb := by unfold OpRegs; decide

/-- `ldV rs a`: the limbs of `[a]` in `rs`. -/
theorem ldV_ok {rs : Nat → Reg} (hrs : OpRegs rs) {a : Nat} (ha : a + 40 ≤ 4096) (ha4 : a % 4 = 0)
    {s : State} (hc : Ctx b s) :
    WP isa (.block (ldV rs a)) s fun s' =>
      (∀ k < 5, (s'.gpr (rs k)).toNat = lw s.mem b a k) ∧ Rest (regs5 rs) s s' ∧ s'.mem = s.mem := by
  rw [ldV_eq]
  refine WP.mono (limbs_ok (rs := rs) (rs' := rs) (tmp := []) (ws := regs5 rs) (val := lw s.mem b a)
    (val' := lw s.mem b a) (fun k hk r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hr; rw [hr]; exact (hrs.2 k hk).1)
    (fun j hj k hk hjk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self, and_self]; exact hrs.1 j hj k hk hjk)
    fun k hk t hr hm => ?_) fun s' ⟨hv, hr, hm⟩ => ⟨fun k hk => (hv k hk).1, hr, hm⟩
  have hct : Ctx b t := hc.of_rest hr fun h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h
    · exact (hrs.2 0 (by decide)).2.1 h.symm
    · exact (hrs.2 1 (by decide)).2.1 h.symm
    · exact (hrs.2 2 (by decide)).2.1 h.symm
    · exact (hrs.2 3 (by decide)).2.1 h.symm
    · exact (hrs.2 4 (by decide)).2.1 h.symm
  refine ld0_ok hct (by omega_using [ha, hk]) (by omega_using [ha4]) fun t1 u1 => WP.block_nil ?_
  have e : (t1.gpr (rs k)).toNat = lw s.mem b a k := by rw [u1.gpr, hm]; rfl
  exact ⟨e, e, u1.rest (by simp), u1.mem⟩

/-! ## Sums and differences as operands -/

/-- Limb `k` of `[a] ± [c]` into `d`. -/
def opnd (sub : Bool) (d : Reg) (a c k : Nat) : List Instr :=
  [.load .d d .r6 (a + 8 * k), .load .d .r8 .r6 (c + 8 * k)] ++
    (if sub then [.add d d (twoP k), .sub d d .r8] else [.add d d .r8])

/-- Limb `k` of a sum, or of a difference with `2p`'s limb added. -/
def opv (sub : Bool) (x y : Nat → Nat) (k : Nat) : Nat := if sub then x k + twoPv k - y k else x k + y k

theorem opv_lt {sub : Bool} {x y : Nat → Nat} {k : Nat} (hx : x k < 2 ^ 51 + 2 ^ 18) (hy : y k < 2 ^ 51 + 2 ^ 18) :
    opv sub x y k < 2 ^ 53 := by
  cases sub
  · simp only [opv, Bool.false_eq_true, ↓reduceIte]; omega_using [hx, hy]
  · simp only [opv, twoPv, ↓reduceIte]; split <;> omega_using [hx, hy]

/-- The constants of a difference: `2p`'s limbs in `r9` and `r5`. -/
def SubC (s : State) : Prop := (s.gpr .r9).toNat = twoPv 0 ∧ (s.gpr .r5).toNat = twoPv 1

theorem SubC.twoP {s : State} (h : SubC s) (k : Nat) : (s.gpr (twoP k)).toNat = twoPv k := by
  unfold Impl.X25519.PPC64LE.Fe51.twoP twoPv
  split
  · exact h.1
  · exact h.2

theorem SubC.of_rest {s s' : State} {ws : List Reg} (h : SubC s) (hr : Rest ws s s') (h9 : Reg.r9 ∉ ws)
    (h5 : Reg.r5 ∉ ws) : SubC s' := by
  unfold SubC; rw [hr.gpr _ h9, hr.gpr _ h5]; exact h

theorem subConsts_ok {s : State} :
    WP isa (.block subConsts) s fun s' => SubC s' ∧ Rest [.r5, .r9] s s' ∧ s'.mem = s.mem := by
  refine WP.mono (WP.rest [.r5, .r9] (Q := fun s' => SubC s' ∧ s'.mem = s.mem) ?_ (by decide +kernel))
    fun _ ⟨⟨h, m⟩, r⟩ => ⟨h, r, m⟩
  crunr [subConsts, SubC]
  decide

theorem opnd_ok {sub : Bool} {d : Reg} {a c k : Nat} (hk : k < 5) (ha : a + 40 ≤ 4096) (ha4 : a % 4 = 0)
    (hc' : c + 40 ≤ 4096) (hc4 : c % 4 = 0) (hd6 : d ≠ .r6) (hd8 : d ≠ .r8) (hd9 : d ≠ .r9) (hd5 : d ≠ .r5)
    {t : State} (hct : Ctx b t) (hs : sub = true → SubC t) (ta : Tight t.mem b a) (tc : Tight t.mem b c)
    {is : List Instr} {Q : State → Prop}
    (kont : ∀ t', (t'.gpr d).toNat = opv sub (lw t.mem b a) (lw t.mem b c) k → Rest [d, .r8] t t' →
      t'.mem = t.mem → WP isa (.block is) t' Q) :
    WP isa (.block (opnd sub d a c k ++ is)) t Q := by
  have la := ta k hk
  have lc := tc k hk
  simp only [opnd, List.cons_append, List.nil_append]
  refine ld0_ok hct (by omega_using [ha, hk]) (by omega_using [ha4]) fun t1 u1 => ?_
  have hc1 : Ctx b t1 := hct.of_rest (u1.rest (ws := [d]) (by simp)) (by simp [hd6.symm])
  refine ld0_ok hc1 (by omega_using [hc', hk]) (by omega_using [hc4]) fun t2 u2 => ?_
  have e1 : (t2.gpr d).toNat = lw t.mem b a k := by rw [u2.other _ hd8, u1.gpr]; rfl
  have e2 : (t2.gpr .r8).toNat = lw t.mem b c k := by rw [u2.gpr, u1.mem]; rfl
  have r2 : Rest [d, .r8] t t2 := (u1.rest (by simp)).trans (u2.rest (by simp))
  have m2 : t2.mem = t.mem := by rw [u2.mem, u1.mem]
  cases sub with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
    refine wp_add fun t3 u3 => kont t3 ?_ (r2.trans (u3.rest (by simp))) (by rw [u3.mem, m2])
    rw [u3.gpr, toNat_add_lt (by rw [e1, e2]; omega_using [la, lc]), e1, e2]; rfl
  | true =>
    simp only [↓reduceIte, List.cons_append, List.nil_append]
    have hp : (t2.gpr (twoP k)).toNat = twoPv k := by
      have := (hs rfl).twoP k
      rw [← this]
      unfold Impl.X25519.PPC64LE.Fe51.twoP
      split
      · rw [u2.other _ (by decide), u1.other _ (Ne.symm hd9)]
      · rw [u2.other _ (by decide), u1.other _ (Ne.symm hd5)]
    have hpl : twoPv k = 2 ^ 52 - 38 ∨ twoPv k = 2 ^ 52 - 2 := by unfold twoPv; split <;> simp
    refine wp_add fun t3 u3 => wp_sub fun t4 u4 => kont t4 ?_
      (r2.trans ((u3.rest (by simp)).trans (u4.rest (by simp)))) (by rw [u4.mem, u3.mem, m2])
    have e3 : (t3.gpr d).toNat = lw t.mem b a k + twoPv k := by
      rw [u3.gpr, toNat_add_lt (by rw [e1, hp]; omega_using [la, hpl]), e1, hp]
    rw [u4.gpr, toNat_sub_le (by rw [u3.other _ (Ne.symm hd8), e2, e3]; omega_using [lc, hpl]), e3,
      u3.other _ (Ne.symm hd8), e2]
    rfl

theorem ldOp_eq (sub : Bool) (rs : Nat → Reg) (a c : Nat) :
    (if sub then ldSub rs a c else ldAdd rs a c) = (List.range 5).flatMap fun k => opnd sub (rs k) a c k ++ [] := by
  cases sub <;> rfl

/-- `ldAdd` and `ldSub`: the limbs of `[a] ± [c]` in `rs`. -/
theorem ldOp_ok (sub : Bool) {rs : Nat → Reg} (hrs : OpRegs rs) {a c : Nat} (ha : a + 40 ≤ 4096)
    (ha4 : a % 4 = 0) (hc' : c + 40 ≤ 4096) (hc4 : c % 4 = 0) {s : State} (hc : Ctx b s)
    (hs : sub = true → SubC s) (ta : Tight s.mem b a) (tc : Tight s.mem b c) :
    WP isa (.block (if sub then ldSub rs a c else ldAdd rs a c)) s fun s' =>
      (∀ k < 5, (s'.gpr (rs k)).toNat = opv sub (lw s.mem b a) (lw s.mem b c) k) ∧
      Rest (.r8 :: regs5 rs) s s' ∧ s'.mem = s.mem := by
  rw [ldOp_eq]
  have h6 : Reg.r6 ∉ Reg.r8 :: regs5 rs := fun h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or] at h
    rcases h with h | h | h | h | h
    · exact (hrs.2 0 (by decide)).2.1 h.symm
    · exact (hrs.2 1 (by decide)).2.1 h.symm
    · exact (hrs.2 2 (by decide)).2.1 h.symm
    · exact (hrs.2 3 (by decide)).2.1 h.symm
    · exact (hrs.2 4 (by decide)).2.1 h.symm
  have h95 : Reg.r9 ∉ Reg.r8 :: regs5 rs ∧ Reg.r5 ∉ Reg.r8 :: regs5 rs := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or] at h <;>
      rcases h with h | h | h | h | h
    · exact (hrs.2 0 (by decide)).2.2.2.1 h.symm
    · exact (hrs.2 1 (by decide)).2.2.2.1 h.symm
    · exact (hrs.2 2 (by decide)).2.2.2.1 h.symm
    · exact (hrs.2 3 (by decide)).2.2.2.1 h.symm
    · exact (hrs.2 4 (by decide)).2.2.2.1 h.symm
    · exact (hrs.2 0 (by decide)).2.2.2.2.1 h.symm
    · exact (hrs.2 1 (by decide)).2.2.2.2.1 h.symm
    · exact (hrs.2 2 (by decide)).2.2.2.2.1 h.symm
    · exact (hrs.2 3 (by decide)).2.2.2.2.1 h.symm
    · exact (hrs.2 4 (by decide)).2.2.2.2.1 h.symm
  refine WP.mono (limbs_ok (rs := rs) (rs' := rs) (tmp := [.r8]) (ws := .r8 :: regs5 rs)
    (val := opv sub (lw s.mem b a) (lw s.mem b c)) (val' := opv sub (lw s.mem b a) (lw s.mem b c))
    (fun k hk r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left] at hr
      rcases hr with rfl | rfl
      · exact List.mem_cons_of_mem _ (hrs.2 k hk).1
      · exact List.mem_cons_self ..)
    (fun j hj k hk hjk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, and_self, not_or]
      exact ⟨hrs.1 j hj k hk hjk, (hrs.2 j hj).2.2.1⟩)
    fun k hk t hr hm => ?_) fun s' ⟨hv, hr, hm⟩ => ⟨fun k hk => (hv k hk).1, hr, hm⟩
  obtain ⟨-, r6, r8, r9, r5, -⟩ := hrs.2 k hk
  refine opnd_ok hk ha ha4 hc' hc4 r6 r8 r9 r5 (hc.of_rest hr h6)
    (fun e => (hs e).of_rest hr h95.1 h95.2) (by rw [hm]; exact ta) (by rw [hm]; exact tc)
    fun t' hv r' m' => WP.block_nil ?_
  rw [hm] at hv
  exact ⟨hv, hv, r'.mono (by simp), m'⟩

theorem sel0r (a c : BitVec 64) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 64 0)) = a := by simp

theorem sel1r (a c : BitVec 64) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 64 1)) = c := by
  have : (0 : BitVec 64) - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm c, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem selStep_eq (sub : Bool) (a c e d k : Nat) :
    selStep sub a c e d k = opnd sub .r7 a c k ++ (opnd sub .r10 e d k ++
      ([.logic .xor .r10 .r10 .r7, .logic .and .r10 .r10 .r4, .logic .xor (ra k) .r7 .r10] : List Instr)) := by
  cases sub <;> rfl

theorem ldSel_eq (sub : Bool) (a c e d : Nat) :
    ldSel sub a c e d = .li .r4 0 :: .sub .r4 .r4 .r0 :: ((if sub then subConsts else []) ++
      (List.range 5).flatMap (selStep sub a c e d)) := by
  cases sub <;> rfl

/-- The registers `ldSel` writes. -/
abbrev selRegs : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r18]

/-- `ldSel`: the limbs of `[a] ± [c]`, or of `[e] ± [d]` if `swap` is 1, in `ra`. -/
theorem ldSel_ok (sub : Bool) {a c e d : Nat} (ha : a + 40 ≤ 4096) (ha4 : a % 4 = 0) (hc' : c + 40 ≤ 4096)
    (hc4 : c % 4 = 0) (he : e + 40 ≤ 4096) (he4 : e % 4 = 0) (hd : d + 40 ≤ 4096) (hd4 : d % 4 = 0)
    {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1) (h0 : s.gpr .r0 = BitVec.ofNat 64 sw)
    (ta : Tight s.mem b a) (tc : Tight s.mem b c) (te : Tight s.mem b e) (td : Tight s.mem b d) :
    WP isa (.block (ldSel sub a c e d)) s fun s' =>
      (∀ k < 5, (s'.gpr (ra k)).toNat = VG.Proof.X25519.sel sw (opv sub (lw s.mem b a) (lw s.mem b c) k)
        (opv sub (lw s.mem b e) (lw s.mem b d) k)) ∧ Rest selRegs s s' ∧ s'.mem = s.mem := by
  rw [ldSel_eq]
  refine wp_li (by decide) fun s1 u1 => wp_sub fun s2 u2 => ?_
  have e4 : s2.gpr .r4 = 0 - BitVec.ofNat 64 sw := by
    rw [u2.gpr, u1.gpr, u1.other _ (by decide), h0]; rfl
  have r2 : Rest selRegs s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hc2 : Ctx b s2 := hc.of_rest r2 (by decide)
  have hpre : WP isa (.block (if sub then subConsts else [])) s2 fun s3 =>
      (sub = true → SubC s3) ∧ Rest [.r5, .r9] s2 s3 ∧ s3.mem = s2.mem := by
    cases sub
    · exact WP.block_nil ⟨fun h => absurd h (by decide), Rest.refl _ _, rfl⟩
    · exact WP.mono subConsts_ok fun _ ⟨h, r, m⟩ => ⟨fun _ => h, r, m⟩
  refine WP.append hpre fun s3 ⟨hs3, r3, m3⟩ => ?_
  have e43 : s3.gpr .r4 = 0 - BitVec.ofNat 64 sw := by rw [r3.gpr _ (by decide), e4]
  have hc3 : Ctx b s3 := hc2.of_rest r3 (by decide)
  have m3' : s3.mem = s.mem := m3.trans m2
  refine WP.mono (limbs_ok (rs := ra) (rs' := ra) (tmp := [.r7, .r8, .r10]) (ws := [.r7, .r8, .r10, .r14, .r15, .r16, .r17, .r18])
    (val := fun k => VG.Proof.X25519.sel sw (opv sub (lw s.mem b a) (lw s.mem b c) k)
        (opv sub (lw s.mem b e) (lw s.mem b d) k)) (val' := fun k => VG.Proof.X25519.sel sw (opv sub (lw s.mem b a) (lw s.mem b c) k)
        (opv sub (lw s.mem b e) (lw s.mem b d) k)) (by decide) (fun j hj k hk hjk => by
      have hne : ra j ≠ ra k := opRegs_ra.1 j hj k hk hjk
      obtain ⟨-, -, k8, -, -, -, k7, k10⟩ := opRegs_ra.2 j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, and_self]
      exact ⟨hne, hne, k7, k8, k10⟩) fun k hk t hr hm => ?_)
    fun s' ⟨hv, hr, hm⟩ => ⟨fun k hk => (hv k hk).1, r2.trans ((r3.mono (by decide)).trans (hr.mono (by decide))),
      hm.trans m3'⟩
  rw [selStep_eq]
  have hct : Ctx b t := hc3.of_rest hr (by decide)
  have hst : sub = true → SubC t := fun h => (hs3 h).of_rest hr (by decide) (by decide)
  have mt : t.mem = s.mem := hm.trans m3'
  refine opnd_ok hk ha ha4 hc' hc4 (by decide) (by decide) (by decide) (by decide) hct hst
    (by rw [mt]; exact ta) (by rw [mt]; exact tc) fun t1 v1 r1 m1 => ?_
  refine opnd_ok hk he he4 hd hd4 (by decide) (by decide) (by decide) (by decide)
    (hct.of_rest r1 (by decide)) (fun h => (hst h).of_rest r1 (by decide) (by decide))
    (by rw [m1, mt]; exact te) (by rw [m1, mt]; exact td) fun t2 v2 r2' m2' => ?_
  refine wp_xor fun t3 u3 => wp_and fun t4 u4 => wp_xor fun t5 u5 => WP.block_nil ?_
  obtain ⟨-, k6, k8, -, -, k4, k7, k10⟩ := opRegs_ra.2 k hk
  have g7 : t4.gpr .r7 = t1.gpr .r7 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), r2'.gpr _ (by decide)]
  have g4 : t3.gpr .r4 = 0 - BitVec.ofNat 64 sw := by
    rw [u3.other _ (by decide), r2'.gpr _ (by decide), r1.gpr _ (by decide), hr.gpr _ (by decide), e43]
  have val : t5.gpr (ra k) = t1.gpr .r7 ^^^ ((t2.gpr .r10 ^^^ t1.gpr .r7) &&& (0 - BitVec.ofNat 64 sw)) := by
    rw [u5.gpr, g7, u4.gpr, g4, u3.gpr, r2'.gpr .r7 (by decide)]
  have e : (t5.gpr (ra k)).toNat = VG.Proof.X25519.sel sw (opv sub (lw s.mem b a) (lw s.mem b c) k)
        (opv sub (lw s.mem b e) (lw s.mem b d) k) := by
    rw [val]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0r, v1, mt]; rfl
    · rw [sel1r, v2, m1, mt]; rfl
  refine ⟨e, e, ?_, by rw [u5.mem, u4.mem, u3.mem, m2', m1]⟩
  exact (r1.mono (by simp)).trans ((r2'.mono (by simp)).trans ((u3.rest (by simp)).trans
    ((u4.rest (by simp)).trans (u5.rest (by simp)))))

/-! ## Products and squares of operands -/

/-- What a field operation storing the element `val` at `o` leaves. -/
def OpPost (b : Addr) (o : Nat) (val : Fe) (s s' : State) : Prop :=
  Rest coreRegs s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 40⟩] s.mem s'.mem ∧ Tight s'.mem b o ∧
    FS s'.mem b o = val ∧ LoOk b o s'

theorem mulOp_ok {pre : List Instr} {o : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) {s : State}
    (hc : Ctx b s) {a c : Nat → Nat} {ws : List Reg} (hws : ∀ r ∈ ws, r ∈ coreRegs)
    (hpre : WP isa (.block pre) s fun s1 => (∀ i < 5, (s1.gpr (ra i)).toNat = a i) ∧
      (∀ j < 5, (s1.gpr (rb j)).toNat = c j) ∧ Rest ws s s1 ∧ s1.mem = s.mem)
    (ba : ∀ i < 5, a i < 2 ^ 53) (bc : ∀ j < 5, c j < 2 ^ 53) :
    WP isa (.block (pre ++ mulCore o)) s (OpPost b o (toFe (val5 a) * toFe (val5 c)) s) :=
  WP.append hpre fun s1 ⟨ha, hb, r1, m1⟩ =>
    WP.mono (mulCore_ok ho ho4 (hc.of_rest r1 fun h => absurd (hws _ h) (by decide)) ha hb ba bc)
      fun _ ⟨r2, f2, t2, v2, l2⟩ =>
        ⟨(r1.mono hws).trans r2, by rw [← m1]; exact f2, t2, VG.Proof.X25519.toFe_mul v2, l2⟩

theorem sqrOp_ok {pre : List Instr} {o : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) {s : State}
    (hc : Ctx b s) {a : Nat → Nat} {ws : List Reg} (hws : ∀ r ∈ ws, r ∈ coreRegs)
    (hpre : WP isa (.block pre) s fun s1 => (∀ i < 5, (s1.gpr (ra i)).toNat = a i) ∧ Rest ws s s1 ∧
      s1.mem = s.mem)
    (ba : ∀ i < 5, a i < 2 ^ 53) :
    WP isa (.block (pre ++ sqrCore o)) s (OpPost b o (toFe (val5 a) * toFe (val5 a)) s) :=
  WP.append hpre fun s1 ⟨ha, r1, m1⟩ =>
    WP.mono (sqrCore_ok ho ho4 (hc.of_rest r1 fun h => absurd (hws _ h) (by decide)) ha ba)
      fun _ ⟨r2, f2, t2, v2, l2⟩ =>
        ⟨(r1.mono hws).trans r2, by rw [← m1]; exact f2, t2, VG.Proof.X25519.toFe_mul v2, l2⟩

theorem Tight.lt53 {m : Mem} {o : Nat} (h : Tight m b o) : ∀ k < 5, lw m b o k < 2 ^ 53 := fun k hk => by
  have := h k hk; omega_using [this]

theorem ra_rb : ∀ i < 5, ra i ∉ regs5 rb ∧ ra i ∉ Reg.r8 :: regs5 rb := by decide

/-- The element of a sum or a difference of limbs. -/
theorem fe_opv (sub : Bool) {x y : Nat → Nat} (hy : ∀ k < 5, y k < 2 ^ 51 + 2 ^ 18) :
    toFe (val5 (opv sub x y)) =
      if sub then toFe (val5 x) - toFe (val5 y) else toFe (val5 x) + toFe (val5 y) := by
  cases sub
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact VG.Proof.X25519.toFe_add (congrArg (· % P) (val5_add x y))
  · simp only [↓reduceIte]
    refine toFe_dif (val5_sub fun k hk => ?_)
    have := hy k hk
    simp only [opv, ↓reduceIte, twoPv]
    split <;> omega_using [this]

/-- `[o] = [x] · [y]`. -/
theorem mul_ok {o x y : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) (hx : x + 40 ≤ 4096) (hx4 : x % 4 = 0)
    (hy : y + 40 ≤ 4096) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) (tx : Tight s.mem b x)
    (ty : Tight s.mem b y) :
    WP isa (.block (mul o x y)) s (OpPost b o (FS s.mem b x * FS s.mem b y) s) := by
  refine mulOp_ok (ws := regs5 ra ++ regs5 rb) ho ho4 hc (by decide) ?_ tx.lt53 ty.lt53
  refine WP.append (ldV_ok opRegs_ra hx hx4 hc) fun s1 ⟨v1, r1, m1⟩ => ?_
  refine WP.mono (ldV_ok opRegs_rb hy hy4 (hc.of_rest r1 (by decide))) fun s2 ⟨v2, r2, m2⟩ =>
    ⟨fun i hi => by rw [r2.gpr _ (ra_rb i hi).1]; exact v1 i hi, fun j hj => by rw [v2 j hj, m1],
      (r1.mono (by decide)).trans (r2.mono (by decide)), m2.trans m1⟩

/-- `[o] = [x]²`. -/
theorem sqr_ok {o x : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) (hx : x + 40 ≤ 4096) (hx4 : x % 4 = 0)
    {s : State} (hc : Ctx b s) (tx : Tight s.mem b x) :
    WP isa (.block (sqr o x)) s (OpPost b o (FS s.mem b x * FS s.mem b x) s) :=
  sqrOp_ok (ws := regs5 ra) ho ho4 hc (by decide) (ldV_ok opRegs_ra hx hx4 hc) tx.lt53

/-- `[o]` is the square of the element `[x]` that `lo` holds. -/
theorem sqrL_ok {o x : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s)
    (tx : Tight s.mem b x) (hl : LoOk b x s) :
    WP isa (.block (sqrL o)) s (OpPost b o (FS s.mem b x * FS s.mem b x) s) := by
  refine sqrOp_ok (ws := regs5 ra) ho ho4 hc (by decide) ?_ tx.lt53
  refine WP.mono (WP.rest (regs5 ra) (Q := fun s1 => (∀ i < 5, (s1.gpr (ra i)).toNat = lw s.mem b x i) ∧
    s1.mem = s.mem) ?_ (by decide +kernel)) fun _ ⟨⟨h, m⟩, r⟩ => ⟨h, r, m⟩
  have l0 := hl 0 (by decide); have l1 := hl 1 (by decide); have l2 := hl 2 (by decide)
  have l3 := hl 3 (by decide); have l4 := hl 4 (by decide)
  simp only [lo, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at l0 l1 l2 l3 l4
  crunr [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, ra, lo, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, BitVec.or_self]
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega_using [hi]
  rcases this with rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, reduceCtorEq, ↓reduceIte] <;>
    with_reducible assumption

theorem ldSub_ok {rs : Nat → Reg} (hrs : OpRegs rs) {a c : Nat} (ha : a + 40 ≤ 4096) (ha4 : a % 4 = 0)
    (hc' : c + 40 ≤ 4096) (hc4 : c % 4 = 0) {s : State} (hc : Ctx b s) (hs : SubC s)
    (ta : Tight s.mem b a) (tc : Tight s.mem b c) :
    WP isa (.block (ldSub rs a c)) s fun s' =>
      (∀ k < 5, (s'.gpr (rs k)).toNat = opv true (lw s.mem b a) (lw s.mem b c) k) ∧
      Rest (.r8 :: regs5 rs) s s' ∧ s'.mem = s.mem :=
  ldOp_ok true hrs ha ha4 hc' hc4 hc (fun _ => hs) ta tc

theorem ldAdd_ok {rs : Nat → Reg} (hrs : OpRegs rs) {a c : Nat} (ha : a + 40 ≤ 4096) (ha4 : a % 4 = 0)
    (hc' : c + 40 ≤ 4096) (hc4 : c % 4 = 0) {s : State} (hc : Ctx b s)
    (ta : Tight s.mem b a) (tc : Tight s.mem b c) :
    WP isa (.block (ldAdd rs a c)) s fun s' =>
      (∀ k < 5, (s'.gpr (rs k)).toNat = opv false (lw s.mem b a) (lw s.mem b c) k) ∧
      Rest (.r8 :: regs5 rs) s s' ∧ s'.mem = s.mem :=
  ldOp_ok false hrs ha ha4 hc' hc4 hc (fun h => absurd h (by decide)) ta tc

/-- `[o] = ([a] - [c]) · ([e] + [d])`. -/
theorem mulDS_ok {o a c e d : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) (ha : a + 40 ≤ 4096)
    (ha4 : a % 4 = 0) (hc' : c + 40 ≤ 4096) (hc4 : c % 4 = 0) (he : e + 40 ≤ 4096) (he4 : e % 4 = 0)
    (hd : d + 40 ≤ 4096) (hd4 : d % 4 = 0) {s : State} (hc : Ctx b s) (ta : Tight s.mem b a)
    (tc : Tight s.mem b c) (te : Tight s.mem b e) (td : Tight s.mem b d) :
    WP isa (.block (mulDS o a c e d)) s
      (OpPost b o ((FS s.mem b a - FS s.mem b c) * (FS s.mem b e + FS s.mem b d)) s) := by
  have h := mulOp_ok (b := b) (o := o) (pre := subConsts ++ ldSub ra a c ++ ldAdd rb e d)
    (a := opv true (lw s.mem b a) (lw s.mem b c)) (c := opv false (lw s.mem b e) (lw s.mem b d))
    (ws := [.r5, .r9, .r8] ++ regs5 ra ++ regs5 rb) ho ho4 hc (by decide) ?_
    (fun i hi => opv_lt (ta i hi) (tc i hi)) (fun j hj => opv_lt (te j hj) (td j hj))
  · rw [fe_opv true tc, fe_opv false td] at h; exact h
  · rw [List.append_assoc]
    refine WP.append subConsts_ok fun s1 ⟨hs1, r1, m1⟩ => ?_
    have hc1 := hc.of_rest r1 (by decide)
    refine WP.append (ldSub_ok opRegs_ra ha ha4 hc' hc4 hc1 hs1 (by rw [m1]; exact ta) (by rw [m1]; exact tc))
      fun s2 ⟨v2, r2, m2⟩ => ?_
    refine WP.mono (ldAdd_ok opRegs_rb he he4 hd hd4 (hc1.of_rest r2 (by decide)) (by rw [m2, m1]; exact te)
      (by rw [m2, m1]; exact td)) fun s3 ⟨v3, r3, m3⟩ =>
      ⟨fun i hi => by rw [r3.gpr _ (ra_rb i hi).2, v2 i hi, m1], fun j hj => by rw [v3 j hj, m2, m1],
        (r1.mono (by decide)).trans ((r2.mono (by decide)).trans (r3.mono (by decide))), by rw [m3, m2, m1]⟩

/-- `[o] = ([a] - [c]) · [e]`. -/
theorem mulSub_ok {o a c e : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) (ha : a + 40 ≤ 4096)
    (ha4 : a % 4 = 0) (hc' : c + 40 ≤ 4096) (hc4 : c % 4 = 0) (he : e + 40 ≤ 4096) (he4 : e % 4 = 0)
    {s : State} (hc : Ctx b s) (ta : Tight s.mem b a) (tc : Tight s.mem b c) (te : Tight s.mem b e) :
    WP isa (.block (mulSub o a c e)) s (OpPost b o ((FS s.mem b a - FS s.mem b c) * FS s.mem b e) s) := by
  have h := mulOp_ok (b := b) (o := o) (pre := subConsts ++ ldSub ra a c ++ ldV rb e)
    (a := opv true (lw s.mem b a) (lw s.mem b c)) (c := lw s.mem b e)
    (ws := [.r5, .r9, .r8] ++ regs5 ra ++ regs5 rb) ho ho4 hc (by decide) ?_
    (fun i hi => opv_lt (ta i hi) (tc i hi)) te.lt53
  · rw [fe_opv true tc] at h; exact h
  · rw [List.append_assoc]
    refine WP.append subConsts_ok fun s1 ⟨hs1, r1, m1⟩ => ?_
    have hc1 := hc.of_rest r1 (by decide)
    refine WP.append (ldSub_ok opRegs_ra ha ha4 hc' hc4 hc1 hs1 (by rw [m1]; exact ta) (by rw [m1]; exact tc))
      fun s2 ⟨v2, r2, m2⟩ => ?_
    refine WP.mono (ldV_ok opRegs_rb he he4 (hc1.of_rest r2 (by decide))) fun s3 ⟨v3, r3, m3⟩ =>
      ⟨fun i hi => by rw [r3.gpr _ (ra_rb i hi).1, v2 i hi, m1], fun j hj => by rw [v3 j hj, m2, m1],
        (r1.mono (by decide)).trans ((r2.mono (by decide)).trans (r3.mono (by decide))), by rw [m3, m2, m1]⟩

/-- `[o] = ([a] + [c])²`. -/
theorem sqrAdd_ok {o a c : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) (ha : a + 40 ≤ 4096)
    (ha4 : a % 4 = 0) (hc' : c + 40 ≤ 4096) (hc4 : c % 4 = 0) {s : State} (hc : Ctx b s)
    (ta : Tight s.mem b a) (tc : Tight s.mem b c) :
    WP isa (.block (sqrAdd o a c)) s
      (OpPost b o ((FS s.mem b a + FS s.mem b c) * (FS s.mem b a + FS s.mem b c)) s) := by
  have h := sqrOp_ok (b := b) (o := o) (ws := .r8 :: regs5 ra) ho ho4 hc (by decide)
    (ldAdd_ok opRegs_ra ha ha4 hc' hc4 hc ta tc) fun i hi => opv_lt (ta i hi) (tc i hi)
  rw [fe_opv false tc] at h; exact h

/-- `[o] = ([a] - [c])²`. -/
theorem sqrSub_ok {o a c : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) (ha : a + 40 ≤ 4096)
    (ha4 : a % 4 = 0) (hc' : c + 40 ≤ 4096) (hc4 : c % 4 = 0) {s : State} (hc : Ctx b s)
    (ta : Tight s.mem b a) (tc : Tight s.mem b c) :
    WP isa (.block (sqrSub o a c)) s
      (OpPost b o ((FS s.mem b a - FS s.mem b c) * (FS s.mem b a - FS s.mem b c)) s) := by
  have h := sqrOp_ok (b := b) (o := o) (pre := subConsts ++ ldSub ra a c)
    (a := opv true (lw s.mem b a) (lw s.mem b c)) (ws := [.r5, .r9, .r8] ++ regs5 ra) ho ho4 hc (by decide) ?_
    fun i hi => opv_lt (ta i hi) (tc i hi)
  · rw [fe_opv true tc] at h; exact h
  · refine WP.append subConsts_ok fun s1 ⟨hs1, r1, m1⟩ => ?_
    refine WP.mono (ldSub_ok opRegs_ra ha ha4 hc' hc4 (hc.of_rest r1 (by decide)) hs1 (by rw [m1]; exact ta)
      (by rw [m1]; exact tc)) fun s2 ⟨v2, r2, m2⟩ =>
      ⟨fun i hi => by rw [v2 i hi, m1], (r1.mono (by decide)).trans (r2.mono (by decide)), m2.trans m1⟩

/-- `[o] = ([a] ± [c])²`, or `([e] ± [d])²` if `swap` is 1. -/
theorem sqrSel_ok (sub : Bool) {o a c e d : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) (ha : a + 40 ≤ 4096)
    (ha4 : a % 4 = 0) (hc' : c + 40 ≤ 4096) (hc4 : c % 4 = 0) (he : e + 40 ≤ 4096) (he4 : e % 4 = 0)
    (hd : d + 40 ≤ 4096) (hd4 : d % 4 = 0) {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1)
    (h0 : s.gpr .r0 = BitVec.ofNat 64 sw) (ta : Tight s.mem b a) (tc : Tight s.mem b c)
    (te : Tight s.mem b e) (td : Tight s.mem b d) :
    WP isa (.block (sqrSel o sub a c e d)) s
      (OpPost b o
        (let x := VG.Proof.X25519.sel sw
          (if sub then FS s.mem b a - FS s.mem b c else FS s.mem b a + FS s.mem b c)
          (if sub then FS s.mem b e - FS s.mem b d else FS s.mem b e + FS s.mem b d)
        x * x) s) := by
  have h := sqrOp_ok (b := b) (o := o) (ws := selRegs) ho ho4 hc (by decide)
    (ldSel_ok sub ha ha4 hc' hc4 he he4 hd hd4 hc hsw h0 ta tc te td) fun i hi => by
      unfold VG.Proof.X25519.sel; split
      · exact opv_lt (te i hi) (td i hi)
      · exact opv_lt (ta i hi) (tc i hi)
  have e : toFe (val5 fun k => VG.Proof.X25519.sel sw (opv sub (lw s.mem b a) (lw s.mem b c) k)
      (opv sub (lw s.mem b e) (lw s.mem b d) k)) = VG.Proof.X25519.sel sw
        (if sub then FS s.mem b a - FS s.mem b c else FS s.mem b a + FS s.mem b c)
        (if sub then FS s.mem b e - FS s.mem b d else FS s.mem b e + FS s.mem b d) := by
    unfold VG.Proof.X25519.sel
    split
    · exact fe_opv sub td
    · exact fe_opv sub tc
  rw [e] at h
  exact h

/-! ## `a + a24 (a - c)` -/

theorem a24Steps_eq (a c : Nat) : (List.range 5).flatMap (a24Step a c) =
    (List.range 5).flatMap fun k => a24Step a c k := rfl

/-- The limbs of `[a]` in `rb` and those of `[a] - [c]`, shifted left by 11, in `ra`. -/
theorem a24Steps_ok {a c : Nat} (ha : a + 40 ≤ 4096) (ha4 : a % 4 = 0) (hc' : c + 40 ≤ 4096)
    (hc4 : c % 4 = 0) {s : State} (hc : Ctx b s) (hs : SubC s) (ta : Tight s.mem b a)
    (tc : Tight s.mem b c) :
    WP isa (.block ((List.range 5).flatMap (a24Step a c))) s fun s' =>
      (∀ k < 5, (s'.gpr (ra k)).toNat = opv true (lw s.mem b a) (lw s.mem b c) k * 2 ^ 11 ∧
        (s'.gpr (rb k)).toNat = lw s.mem b a k) ∧
      Rest (.r8 :: regs5 ra ++ regs5 rb) s s' ∧ s'.mem = s.mem := by
  refine limbs_ok (rs := ra) (rs' := rb) (tmp := [.r8]) (by decide) (fun j hj k hk hjk => ?_)
    fun k hk t hr hm => ?_
  · have h1 := opRegs_ra.1 j hj k hk hjk; have h2 := opRegs_rb.1 j hj k hk hjk
    obtain ⟨-, -, a8, -⟩ := opRegs_ra.2 j hj
    obtain ⟨-, -, b8, -⟩ := opRegs_rb.2 j hj
    have h3 : ∀ i < 5, ∀ j < 5, ra i ≠ rb j := by decide
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨h1, h3 j hj k hk, a8⟩, fun e => h3 k hk j hj e.symm, h2, b8⟩
  have la := ta k hk
  have lc := tc k hk
  obtain ⟨-, a6, a8, a9, a5, -⟩ := opRegs_ra.2 k hk
  obtain ⟨-, b6, b8, b9, b5, -⟩ := opRegs_rb.2 k hk
  have hab : ra k ≠ rb k := (by decide : ∀ i < 5, ra i ≠ rb i) k hk
  have hct : Ctx b t := hc.of_rest hr (by decide)
  have hst : SubC t := hs.of_rest hr (by decide) (by decide)
  simp only [a24Step]
  refine ld0_ok hct (by omega_using [ha, hk]) (by omega_using [ha4]) fun t1 u1 => ?_
  have hc1 : Ctx b t1 := hct.of_rest (u1.rest (ws := [rb k]) (by simp)) (by simp [b6.symm])
  refine ld0_ok hc1 (by omega_using [hc', hk]) (by omega_using [hc4]) fun t2 u2 => ?_
  have e1 : (t2.gpr (rb k)).toNat = lw s.mem b a k := by rw [u2.other _ b8, u1.gpr, hm]; rfl
  have e2 : (t2.gpr .r8).toNat = lw s.mem b c k := by rw [u2.gpr, u1.mem, hm]; rfl
  have hp : (t2.gpr (twoP k)).toNat = twoPv k := by
    have := hst.twoP k
    rw [← this]
    unfold Impl.X25519.PPC64LE.Fe51.twoP
    split
    · rw [u2.other _ (by decide), u1.other _ (Ne.symm b9)]
    · rw [u2.other _ (by decide), u1.other _ (Ne.symm b5)]
  have hpl : twoPv k = 2 ^ 52 - 38 ∨ twoPv k = 2 ^ 52 - 2 := by unfold twoPv; split <;> simp
  refine wp_add fun t3 u3 => wp_sub fun t4 u4 => wp_lsl (by decide) fun t5 u5 => WP.block_nil ?_
  have e3 : (t3.gpr (ra k)).toNat = lw s.mem b a k + twoPv k := by
    rw [u3.gpr, toNat_add_lt (by rw [e1, hp]; omega_using [la, hpl]), e1, hp]
  have e4 : (t4.gpr (ra k)).toNat = opv true (lw s.mem b a) (lw s.mem b c) k := by
    rw [u4.gpr, toNat_sub_le (by rw [u3.other _ (Ne.symm a8), e2, e3]; omega_using [lc, hpl]), e3,
      u3.other _ (Ne.symm a8), e2]
    rfl
  have b4 := opv_lt (sub := true) la lc
  refine ⟨?_, ?_, ?_, by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]⟩
  · rw [u5.gpr]; exact tn_shl e4 11 (by omega_using [b4])
  · rw [u5.other _ (Ne.symm hab), u4.other _ (Ne.symm hab), u3.other _ (Ne.symm hab)]; exact e1
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans (u5.rest (by simp)))))

/-- `addA24`'s constant and products. -/
def a24Terms : List Term := (List.range 5).map fun k => (true, ra k, .r24, k)

theorem addA24_eq (o a c : Nat) : addA24 o a c =
    subConsts ++ ((List.range 5).flatMap (a24Step a c) ++ (([.lis .r24 1, .ori .r24 .r24 0xdb41, .lsl .r24 .r24 2] : List Instr) ++
      (terms a24Terms ++ ((List.range 5).map (fun k => .add (lo k) (lo k) (rb k)) ++ tail o)))) := by
  simp only [addA24, a24Terms, List.append_assoc]

theorem a24Terms_wf : wfR a24Terms = true ∧ wfN a24Terms (fun _ => 0) = true ∧
    ∀ k < 5, accN a24Terms (fun _ => 0) k = 1 := by decide +kernel

theorem accC_a24 (s : State) : ∀ k < 5, accC s a24Terms (fun _ => 0) k = 0 + pv s (true, ra k, .r24, k) := by
  intro k hk
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega_using [hk]
  rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `[o] = [a] + a24 · ([a] - [c])`. -/
theorem addA24_ok {o a c : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) (ha : a + 40 ≤ 4096)
    (ha4 : a % 4 = 0) (hc' : c + 40 ≤ 4096) (hc4 : c % 4 = 0) {s : State} (hc : Ctx b s)
    (ta : Tight s.mem b a) (tc : Tight s.mem b c) :
    WP isa (.block (addA24 o a c)) s
      (OpPost b o (FS s.mem b a + a24 * (FS s.mem b a - FS s.mem b c)) s) := by
  rw [addA24_eq]
  refine WP.append subConsts_ok fun s1 ⟨hs1, r1, m1⟩ => ?_
  have hc1 := hc.of_rest r1 (by decide)
  refine WP.append (a24Steps_ok ha ha4 hc' hc4 hc1 hs1 (by rw [m1]; exact ta) (by rw [m1]; exact tc))
    fun s2 ⟨v2, r2, m2⟩ => ?_
  rw [m1] at v2
  have hK : WP isa (.block [Instr.lis .r24 1, .ori .r24 .r24 0xdb41, .lsl .r24 .r24 2]) s2 fun s3 =>
      (s3.gpr .r24).toNat = 121665 * 2 ^ 2 ∧ s3.mem = s2.mem := by
    crunr
    decide
  refine WP.append (WP.rest [.r24] hK (by decide +kernel)) fun s3 ⟨⟨k3, m3⟩, r3⟩ => ?_
  have ra3 : ∀ k < 5, (s3.gpr (ra k)).toNat = opv true (lw s.mem b a) (lw s.mem b c) k * 2 ^ 11 :=
    fun k hk => by rw [r3.gpr _ ((by decide : ∀ k < 5, ra k ∉ [Reg.r24]) k hk)]; exact (v2 k hk).1
  have rb3 : ∀ k < 5, (s3.gpr (rb k)).toNat = lw s.mem b a k :=
    fun k hk => by rw [r3.gpr _ ((by decide : ∀ k < 5, rb k ∉ [Reg.r24]) k hk)]; exact (v2 k hk).2
  have hpv : ∀ k < 5, pv s3 (true, ra k, .r24, k) = opv true (lw s.mem b a) (lw s.mem b c) k * 121665 :=
    fun k hk => by rw [pv_def]; exact prod_div (ra3 k hk) k3 rfl
  have hb : ∀ k < 5, opv true (lw s.mem b a) (lw s.mem b c) k < 2 ^ 53 := fun k hk => opv_lt (ta k hk) (tc k hk)
  refine WP.append (terms_ok a24Terms (fun _ => 0) (fun _ => 0) s3 a24Terms_wf.1 a24Terms_wf.2.1 (Acc.zero _ _)
    fun t ht => by
      simp only [a24Terms, List.mem_map, List.mem_range] at ht
      obtain ⟨k, hk, rfl⟩ := ht
      rw [hpv k hk]; have := hb k hk; omega_using [this]) fun s4 ⟨A4, r4, m4⟩ => ?_
  have hn := a24Terms_wf.2.2
  have rb4 : ∀ k < 5, (s4.gpr (rb k)).toNat = lw s.mem b a k :=
    fun k hk => by rw [r4.gpr _ ((by decide : ∀ k < 5, rb k ∉ accRegs) k hk)]; exact rb3 k hk
  have hadd : WP isa (.block ((List.range 5).map fun k => Instr.add (lo k) (lo k) (rb k))) s4 fun s5 =>
      (∀ k < 5, (s5.gpr (lo k)).toNat = (s4.gpr (lo k)).toNat + lw s.mem b a k) ∧ s5.mem = s4.mem := by
    have x0 := rb4 0 (by decide); have x1 := rb4 1 (by decide); have x2 := rb4 2 (by decide)
    have x3 := rb4 3 (by decide); have x4 := rb4 4 (by decide)
    have y0 := A4.low 0 (by decide) (by rw [hn 0 (by decide)]; decide)
    have y1 := A4.low 1 (by decide) (by rw [hn 1 (by decide)]; decide)
    have y2 := A4.low 2 (by decide) (by rw [hn 2 (by decide)]; decide)
    have y3 := A4.low 3 (by decide) (by rw [hn 3 (by decide)]; decide)
    have y4 := A4.low 4 (by decide) (by rw [hn 4 (by decide)]; decide)
    rw [hn 0 (by decide)] at y0; rw [hn 1 (by decide)] at y1; rw [hn 2 (by decide)] at y2
    rw [hn 3 (by decide)] at y3; rw [hn 4 (by decide)] at y4
    have t0 := ta 0 (by decide); have t1 := ta 1 (by decide); have t2 := ta 2 (by decide)
    have t3 := ta 3 (by decide); have t4 := ta 4 (by decide)
    simp only [lo, rb, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at x0 x1 x2 x3 x4 y0 y1 y2 y3 y4
    have z0 := tn_add (x := s4.gpr .r7) rfl x0 (by omega_using [y0, t0]); have z1 := tn_add (x := s4.gpr .r8) rfl x1 (by omega_using [y1, t1])
    have z2 := tn_add (x := s4.gpr .r9) rfl x2 (by omega_using [y2, t2]); have z3 := tn_add (x := s4.gpr .r10) rfl x3 (by omega_using [y3, t3])
    have z4 := tn_add (x := s4.gpr .r11) rfl x4 (by omega_using [y4, t4])
    crunr [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, rb, lo, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
    intro k hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega_using [hk]
    rcases this with rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, reduceCtorEq, ↓reduceIte] <;>
      with_reducible assumption
  refine WP.append (WP.rest [.r7, .r8, .r9, .r10, .r11] hadd (by decide +kernel)) fun s5 ⟨⟨v5, m5⟩, r5⟩ => ?_
  have rAll : Rest coreRegs s s5 := (r1.mono (by decide)).trans ((r2.mono (by decide)).trans
    ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans (r5.mono (by decide)))))
  have mAll : s5.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  have hcol : ∀ k < 5, (s5.gpr (lo k)).toNat + 2 ^ 51 * (s5.gpr (hi k)).toNat =
      opv true (lw s.mem b a) (lw s.mem b c) k * 121665 + lw s.mem b a k := fun k hk => by
    have h1 := A4.val k hk (by rw [hn k hk]; decide)
    rw [accC_a24 s3 k hk, hpv k hk] at h1
    rw [v5 k hk, r5.gpr _ ((by decide : ∀ k < 5, hi k ∉ [Reg.r7, .r8, .r9, .r10, .r11]) k hk)]
    omega_using [h1]
  refine WP.mono (tail_ok ho ho4 (hc.of_rest rAll (by decide)) hcol
    (fun k hk => by
      have := A4.low k hk (by rw [hn k hk]; decide); rw [hn k hk] at this
      have := ta k hk
      rw [v5 k hk]; omega_using [this, ta k hk, A4.low k hk (by rw [hn k hk]; decide), hn k hk])
    (fun k hk => by have := hb k hk; have := ta k hk; omega_using [hb k hk, ta k hk]))
    fun s6 ⟨r6, f6, t6, v6, l6⟩ => ⟨rAll.trans (r6.mono (by decide)), by rw [← mAll]; exact f6, t6, ?_, l6⟩
  have hd : toFe (val5 (opv true (lw s.mem b a) (lw s.mem b c))) = FS s.mem b a - FS s.mem b c := by
    rw [fe_opv true tc]; rfl
  rw [← hd]
  refine VG.Proof.X25519.toFe_addA24 ?_
  rw [v6]
  refine congrArg (· % P) ?_
  simp only [val5, V5]
  omega_using []

end

end VG.Proof.X25519.PPC64LE.Fe51
