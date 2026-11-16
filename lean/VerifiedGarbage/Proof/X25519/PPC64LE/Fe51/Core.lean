module
-- separate module: the five-limb field's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.X25519.PPC64LE.Fe51.Terms
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on PPC64LE, five 51-bit limbs: the product and the square

`mulCore o` stores at `o` an element congruent to the product of the
elements whose limbs, below `2⁵³`, are in `ra` and `rb` (`mulCore_ok`), and
`sqrCore o` one congruent to the square of the element in `ra`
(`sqrCore_ok`): the registers' shifted forms (by `crunr`), the products
(`terms_ok`), the columns' sums (`mul_ident`, `sqr_ident`) and the reduction
(`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE.Fe51

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE.Fe51
open VG.Spec.X25519 (P)

/-- The registers the products and squares write. -/
abbrev coreRegs : List Reg :=
  [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24,
    .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem tn_shl {x : BitVec 64} {a : Nat} (hx : x.toNat = a) (n : Nat) (h : a * 2 ^ n < 2 ^ 64) :
    (x <<< n).toNat = a * 2 ^ n := by
  rw [toNat_shl, hx, Nat.mod_eq_of_lt h]

/-- A product of shifted limbs is below `2¹¹²`. -/
theorem pv_lt {x y : Nat} (hx : x < 2 ^ 62) (hy : y < 2 ^ 63) : x * y / 2 ^ 13 < 2 ^ 112 := by
  have : x * y < 2 ^ 62 * 2 ^ 63 := Nat.mul_lt_mul'' hx hy
  omega_using [this]

theorem Acc.of_rest {c n : Nat → Nat} {s s' : State} {ws : List Reg} (h : Acc c n s) (hr : Rest ws s s')
    (hw : ∀ k < 5, lo k ∉ ws ∧ hi k ∉ ws) : Acc c n s' :=
  ⟨fun k hk hn => by rw [hr.gpr _ (hw k hk).1, hr.gpr _ (hw k hk).2]; exact h.val k hk hn,
    fun k hk hn => by rw [hr.gpr _ (hw k hk).1]; exact h.low k hk hn, h.bnd⟩

section
variable {b : Addr}

/-! ## The product -/

/-- `mulCore` before its products. -/
def mulPrep : List Instr :=
  (List.range 5).map (fun i => .lsl (ra i) (ra i) 8) ++
  (List.range 5).map (fun j => .lsl (rb j) (rb j) 5) ++ [.li .r5 19] ++
  (List.range 4).map (fun j => .mul (rn (j + 1)) (rb (j + 1)) .r5)

theorem mulCore_eq (o : Nat) : mulCore o = mulPrep ++ (terms mulTerms ++ tail o) := by
  rw [← List.append_assoc]; rfl

theorem mulPrep_writes : writesOnly [.r5, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24,
    .r25, .r26, .r27] (.block mulPrep) = true := by decide +kernel

theorem mulTerms_wf : wfR mulTerms = true ∧ wfN mulTerms (fun _ => 0) = true ∧
    ∀ k < 5, accN mulTerms (fun _ => 0) k = 5 := by decide +kernel

theorem mulTerms_regs : ∀ t ∈ mulTerms, t.2.1 ∈ [Reg.r14, .r15, .r16, .r17, .r18] ∧
    t.2.2.1 ∈ [Reg.r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27] := by decide +kernel

theorem accC_mul0 (s : State) : accC s mulTerms (fun _ => 0) 0 =
    0 + pv s (true, .r14, .r19, 0) + pv s (false, .r15, .r27, 0) + pv s (false, .r16, .r26, 0) + pv s (false, .r17, .r25, 0) + pv s (false, .r18, .r24, 0) := rfl

theorem accC_mul1 (s : State) : accC s mulTerms (fun _ => 0) 1 =
    0 + pv s (true, .r14, .r20, 1) + pv s (false, .r15, .r19, 1) + pv s (false, .r16, .r27, 1) + pv s (false, .r17, .r26, 1) + pv s (false, .r18, .r25, 1) := rfl

theorem accC_mul2 (s : State) : accC s mulTerms (fun _ => 0) 2 =
    0 + pv s (true, .r14, .r21, 2) + pv s (false, .r15, .r20, 2) + pv s (false, .r16, .r19, 2) + pv s (false, .r17, .r27, 2) + pv s (false, .r18, .r26, 2) := rfl

theorem accC_mul3 (s : State) : accC s mulTerms (fun _ => 0) 3 =
    0 + pv s (true, .r14, .r22, 3) + pv s (false, .r15, .r21, 3) + pv s (false, .r16, .r20, 3) + pv s (false, .r17, .r19, 3) + pv s (false, .r18, .r27, 3) := rfl

theorem accC_mul4 (s : State) : accC s mulTerms (fun _ => 0) 4 =
    0 + pv s (true, .r14, .r23, 4) + pv s (false, .r15, .r22, 4) + pv s (false, .r16, .r21, 4) + pv s (false, .r17, .r20, 4) + pv s (false, .r18, .r19, 4) := rfl


/-- `mulCore o`: the product of the elements in `ra` and `rb`, at `o`. -/
theorem mulCore_ok {o : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s)
    {a c : Nat → Nat} (ha : ∀ i < 5, (s.gpr (ra i)).toNat = a i) (hb : ∀ j < 5, (s.gpr (rb j)).toNat = c j)
    (ba : ∀ i < 5, a i < 2 ^ 53) (bc : ∀ j < 5, c j < 2 ^ 53) :
    WP isa (.block (mulCore o)) s fun s' =>
      Rest coreRegs s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 40⟩] s.mem s'.mem ∧ Tight s'.mem b o ∧
      V5 s'.mem b o % P = (val5 a * val5 c) % P ∧ ∀ k < 5, (s'.gpr (lo k)).toNat = lw s'.mem b o k := by
  have a0 := ha 0 (by decide); have a1 := ha 1 (by decide); have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide); have a4 := ha 4 (by decide)
  have c0 := hb 0 (by decide); have c1 := hb 1 (by decide); have c2 := hb 2 (by decide)
  have c3 := hb 3 (by decide); have c4 := hb 4 (by decide)
  have ba0 := ba 0 (by decide); have ba1 := ba 1 (by decide); have ba2 := ba 2 (by decide)
  have ba3 := ba 3 (by decide); have ba4 := ba 4 (by decide)
  have bc0 := bc 0 (by decide); have bc1 := bc 1 (by decide); have bc2 := bc 2 (by decide)
  have bc3 := bc 3 (by decide); have bc4 := bc 4 (by decide)
  simp only [ra, rb, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at a0 a1 a2 a3 a4 c0 c1 c2 c3 c4
  have hprep : WP isa (.block mulPrep) s fun s' =>
      (s'.gpr .r14).toNat = a 0 * 2 ^ 8 ∧ (s'.gpr .r15).toNat = a 1 * 2 ^ 8 ∧
      (s'.gpr .r16).toNat = a 2 * 2 ^ 8 ∧ (s'.gpr .r17).toNat = a 3 * 2 ^ 8 ∧
      (s'.gpr .r18).toNat = a 4 * 2 ^ 8 ∧ (s'.gpr .r19).toNat = c 0 * 2 ^ 5 ∧
      (s'.gpr .r20).toNat = c 1 * 2 ^ 5 ∧ (s'.gpr .r21).toNat = c 2 * 2 ^ 5 ∧
      (s'.gpr .r22).toNat = c 3 * 2 ^ 5 ∧ (s'.gpr .r23).toNat = c 4 * 2 ^ 5 ∧
      (s'.gpr .r24).toNat = 19 * c 1 * 2 ^ 5 ∧ (s'.gpr .r25).toNat = 19 * c 2 * 2 ^ 5 ∧
      (s'.gpr .r26).toNat = 19 * c 3 * 2 ^ 5 ∧ (s'.gpr .r27).toNat = 19 * c 4 * 2 ^ 5 ∧ s'.mem = s.mem := by
    have x0 := tn_shl a0 8 (by omega_using [ba0]); have x1 := tn_shl a1 8 (by omega_using [ba1])
    have x2 := tn_shl a2 8 (by omega_using [ba2]); have x3 := tn_shl a3 8 (by omega_using [ba3])
    have x4 := tn_shl a4 8 (by omega_using [ba4])
    have y0 := tn_shl c0 5 (by omega_using [bc0]); have y1 := tn_shl c1 5 (by omega_using [bc1])
    have y2 := tn_shl c2 5 (by omega_using [bc2]); have y3 := tn_shl c3 5 (by omega_using [bc3])
    have y4 := tn_shl c4 5 (by omega_using [bc4])
    have n1 := tn_mul19 y1 (by omega_using [bc1]); have n2 := tn_mul19 y2 (by omega_using [bc2])
    have n3 := tn_mul19 y3 (by omega_using [bc3]); have n4 := tn_mul19 y4 (by omega_using [bc4])
    rw [← Nat.mul_assoc] at n1 n2 n3 n4
    crunr [mulPrep, ra, rb, rn, List.range_succ, List.range_zero, List.map_append, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, List.append_assoc, List.getD_cons_zero,
      List.getD_cons_succ, List.getD_nil]
    exact ⟨x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, n1, n2, n3, n4⟩
  rw [mulCore_eq]
  refine WP.append (WP.rest _ hprep mulPrep_writes)
    fun s1 ⟨⟨x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, n1, n2, n3, n4, m1⟩, r1⟩ => ?_
  have hpv : ∀ t ∈ mulTerms, pv s1 t < 2 ^ 112 := fun t ht => by
    obtain ⟨hx, hy⟩ := mulTerms_regs t ht
    refine pv_lt ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with e | e | e | e | e <;> rw [e] <;>
        omega_using [x0, x1, x2, x3, x4, ba0, ba1, ba2, ba3, ba4]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with e | e | e | e | e | e | e | e | e <;> rw [e] <;>
        omega_using [y0, y1, y2, y3, y4, n1, n2, n3, n4, bc0, bc1, bc2, bc3, bc4]
  refine WP.append (terms_ok mulTerms (fun _ => 0) (fun _ => 0) s1 mulTerms_wf.1 mulTerms_wf.2.1 (Acc.zero _ _) hpv)
    fun s2 ⟨A2, r2, m2⟩ => ?_
  have hn := mulTerms_wf.2.2
  have hc2 : Ctx b s2 := (hc.of_rest r1 (by decide)).of_rest r2 (by decide)
  refine WP.mono (tail_ok ho ho4 hc2 (c := accC s1 mulTerms fun _ => 0)
    (fun k hk => A2.val k hk (by rw [hn k hk]; decide))
    (fun k hk => by have := A2.low k hk (by rw [hn k hk]; decide); rw [hn k hk] at this; omega_using [this])
    (fun k hk => by have := A2.bnd k hk (by rw [hn k hk]; decide); rw [hn k hk] at this; exact this))
    fun s3 ⟨r3, f3, t3, v3, l3⟩ => ⟨(r1.mono (by decide)).trans ((r2.mono (by decide)).trans (r3.mono (by decide))),
      by rw [← m1, ← m2]; exact f3, t3, ?_, l3⟩
  rw [v3]
  have e : val5 a * val5 c = val5 (lim (a 0) (a 1) (a 2) (a 3) (a 4)) * val5 (lim (c 0) (c 1) (c 2) (c 3) (c 4)) := rfl
  rw [e, ← mul_ident, val5, accC_mul0, accC_mul1, accC_mul2, accC_mul3, accC_mul4]
  simp only [pv]
  rw [prod_div x0 y0 rfl, prod_div x1 n4 rfl, prod_div x2 n3 rfl, prod_div x3 n2 rfl, prod_div x4 n1 rfl,
    prod_div x0 y1 rfl, prod_div x1 y0 rfl, prod_div x2 n4 rfl, prod_div x3 n3 rfl, prod_div x4 n2 rfl,
    prod_div x0 y2 rfl, prod_div x1 y1 rfl, prod_div x2 y0 rfl, prod_div x3 n4 rfl, prod_div x4 n3 rfl,
    prod_div x0 y3 rfl, prod_div x1 y2 rfl, prod_div x2 y1 rfl, prod_div x3 y0 rfl, prod_div x4 n4 rfl,
    prod_div x0 y4 rfl, prod_div x1 y3 rfl, prod_div x2 y2 rfl, prod_div x3 y1 rfl, prod_div x4 y0 rfl]

/-! ## The square -/

/-- The blocks of `sqrCore` between its products. -/
def sqrP0 : List Instr :=
  [.lsl .r19 .r14 4, .lsl .r14 .r14 9, .lsl .r20 .r15 5, .lsl .r21 .r16 5, .lsl .r22 .r17 5, .lsl .r23 .r18 5]
def sqrT0 : List Term :=
  [(true, .r14, .r19, 0), (true, .r14, .r20, 1), (true, .r14, .r21, 2), (true, .r14, .r22, 3), (true, .r14, .r23, 4)]
def sqrP1 : List Instr := [.lsl .r19 .r15 4, .lsl .r15 .r15 9, .li .r24 19, .mul .r23 .r23 .r24]
def sqrT1 : List Term :=
  [(false, .r15, .r19, 2), (false, .r15, .r21, 3), (false, .r15, .r22, 4), (false, .r15, .r23, 0)]
def sqrP2 : List Instr := [.lsl .r19 .r16 4, .lsl .r16 .r16 9, .mul .r22 .r22 .r24]
def sqrT2 : List Term := [(false, .r16, .r19, 4), (false, .r16, .r22, 0), (false, .r16, .r23, 1)]

theorem sqrCore_eq (o : Nat) : sqrCore o =
    sqrP0 ++ (terms sqrT0 ++ (sqrP1 ++ (terms sqrT1 ++ (sqrP2 ++ (terms sqrT2 ++
      ([Instr.lsl .r17 .r17 8] ++ (terms [(false, .r17, .r22, 1)] ++ ([Instr.lsl .r17 .r17 1] ++
      (terms [(false, .r17, .r23, 2)] ++ ([Instr.lsl .r18 .r18 8] ++ (terms [(false, .r18, .r23, 3)] ++
      tail o))))))))))) := by
  simp only [sqrCore, sqrP0, sqrT0, sqrP1, sqrT1, sqrP2, sqrT2, List.append_assoc]

/-- The registers the blocks between the products write. -/
abbrev formRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24]

theorem sqr_writes : writesOnly formRegs (.block sqrP0) = true ∧ writesOnly formRegs (.block sqrP1) = true ∧
    writesOnly formRegs (.block sqrP2) = true ∧
    writesOnly [.r17] (.block [Instr.lsl .r17 .r17 8]) = true ∧
    writesOnly [.r17] (.block [Instr.lsl .r17 .r17 1]) = true ∧
    writesOnly [.r18] (.block [Instr.lsl .r18 .r18 8]) = true := by decide +kernel

/-- A block between products: what it leaves in the registers, with what it keeps. -/
theorem form_ok {is : List Instr} {s : State} {Q : State → Prop} {c n : Nat → Nat} {ws : List Reg}
    (h : WP isa (.block is) s Q) (hw : writesOnly ws (.block is) = true) (hA : Acc c n s)
    (hacc : ∀ k < 5, lo k ∉ ws ∧ hi k ∉ ws := by decide) :
    WP isa (.block is) s fun s' => Q s' ∧ Rest ws s s' ∧ Acc c n s' :=
  WP.mono (WP.rest ws h hw) fun _ ⟨hq, hr⟩ => ⟨hq, hr, hA.of_rest hr hacc⟩

theorem pv_def (s : State) (f : Bool) (x y : Reg) (k : Nat) :
    pv s (f, x, y, k) = (s.gpr x).toNat * (s.gpr y).toNat / 2 ^ 13 := rfl

/-- `sqrCore o`: the square of the element in `ra`, at `o`. -/
theorem sqrCore_ok {o : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s)
    {a : Nat → Nat} (ha : ∀ i < 5, (s.gpr (ra i)).toNat = a i) (ba : ∀ i < 5, a i < 2 ^ 53) :
    WP isa (.block (sqrCore o)) s fun s' =>
      Rest coreRegs s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 40⟩] s.mem s'.mem ∧ Tight s'.mem b o ∧
      V5 s'.mem b o % P = (val5 a * val5 a) % P ∧ ∀ k < 5, (s'.gpr (lo k)).toNat = lw s'.mem b o k := by
  have a0 := ha 0 (by decide); have a1 := ha 1 (by decide); have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide); have a4 := ha 4 (by decide)
  have b0 := ba 0 (by decide); have b1 := ba 1 (by decide); have b2 := ba 2 (by decide)
  have b3 := ba 3 (by decide); have b4 := ba 4 (by decide)
  simp only [ra, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at a0 a1 a2 a3 a4
  rw [sqrCore_eq]
  -- `a0`'s products
  have h0 : WP isa (.block sqrP0) s fun s' =>
      (s'.gpr .r19).toNat = a 0 * 2 ^ 4 ∧ (s'.gpr .r14).toNat = a 0 * 2 ^ 9 ∧
      (s'.gpr .r20).toNat = a 1 * 2 ^ 5 ∧ (s'.gpr .r21).toNat = a 2 * 2 ^ 5 ∧
      (s'.gpr .r22).toNat = a 3 * 2 ^ 5 ∧ (s'.gpr .r23).toNat = a 4 * 2 ^ 5 ∧
      (s'.gpr .r15).toNat = a 1 ∧ (s'.gpr .r16).toNat = a 2 ∧ (s'.gpr .r17).toNat = a 3 ∧
      (s'.gpr .r18).toNat = a 4 ∧ s'.mem = s.mem := by
    have q := tn_shl a0 4 (by omega_using [b0]); have d := tn_shl a0 9 (by omega_using [b0])
    have p1 := tn_shl a1 5 (by omega_using [b1]); have p2 := tn_shl a2 5 (by omega_using [b2])
    have p3 := tn_shl a3 5 (by omega_using [b3]); have p4 := tn_shl a4 5 (by omega_using [b4])
    crunr [sqrP0]
    exact ⟨q, d, p1, p2, p3, p4, a1, a2, a3, a4⟩
  refine WP.append (form_ok h0 sqr_writes.1 (Acc.zero (fun _ => 0) s))
    fun s1 ⟨⟨q0, d0, p1, p2, p3, p4, g1, g2, g3, g4, m1⟩, r1, A1⟩ => ?_
  refine WP.append (terms_ok sqrT0 (fun _ => 0) (fun _ => 0) s1 (by decide) (by decide) A1 fun t ht => by
      simp only [sqrT0, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl <;> rw [pv_def] <;> exact pv_lt (by omega_using [d0, b0])
        (by omega_using [q0, p1, p2, p3, p4, b0, b1, b2, b3, b4])) fun s2 ⟨A2, r2, m2⟩ => ?_
  -- `a1`'s
  have h1 : WP isa (.block sqrP1) s2 fun s' =>
      (s'.gpr .r19).toNat = a 1 * 2 ^ 4 ∧ (s'.gpr .r15).toNat = a 1 * 2 ^ 9 ∧
      (s'.gpr .r23).toNat = 19 * a 4 * 2 ^ 5 ∧ (s'.gpr .r24).toNat = 19 ∧
      (s'.gpr .r21).toNat = a 2 * 2 ^ 5 ∧ (s'.gpr .r22).toNat = a 3 * 2 ^ 5 ∧
      (s'.gpr .r16).toNat = a 2 ∧ (s'.gpr .r17).toNat = a 3 ∧ (s'.gpr .r18).toNat = a 4 ∧
      s'.mem = s2.mem := by
    have g1' : (s2.gpr .r15).toNat = a 1 := by rw [r2.gpr _ (by decide)]; exact g1
    have p4' : (s2.gpr .r23).toNat = a 4 * 2 ^ 5 := by rw [r2.gpr _ (by decide)]; exact p4
    have q := tn_shl g1' 4 (by omega_using [b1]); have d := tn_shl g1' 9 (by omega_using [b1])
    have n4 := tn_mul19 p4' (by omega_using [b4])
    rw [← Nat.mul_assoc] at n4
    have e24 : (BitVec.ofNat 64 19).toNat = 19 := rfl
    crunr [sqrP1]
    exact ⟨q, d, n4, e24, by rw [r2.gpr _ (by decide)]; exact p2, by rw [r2.gpr _ (by decide)]; exact p3,
      by rw [r2.gpr _ (by decide)]; exact g2, by rw [r2.gpr _ (by decide)]; exact g3,
      by rw [r2.gpr _ (by decide)]; exact g4⟩
  refine WP.append (form_ok h1 sqr_writes.2.1 A2)
    fun s3 ⟨⟨q1, d1, n4, e24, p2', p3', g2', g3', g4', m3⟩, r3, A3⟩ => ?_
  refine WP.append (terms_ok sqrT1 _ _ s3 (by decide) (by decide) A3 fun t ht => by
      simp only [sqrT1, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> rw [pv_def] <;> exact pv_lt (by omega_using [d1, b1])
        (by omega_using [q1, p2', p3', n4, b1, b2, b3, b4])) fun s4 ⟨A4, r4, m4⟩ => ?_
  -- `a2`'s
  have h2 : WP isa (.block sqrP2) s4 fun s' =>
      (s'.gpr .r19).toNat = a 2 * 2 ^ 4 ∧ (s'.gpr .r16).toNat = a 2 * 2 ^ 9 ∧
      (s'.gpr .r22).toNat = 19 * a 3 * 2 ^ 5 ∧ (s'.gpr .r23).toNat = 19 * a 4 * 2 ^ 5 ∧
      (s'.gpr .r17).toNat = a 3 ∧ (s'.gpr .r18).toNat = a 4 ∧ s'.mem = s4.mem := by
    have g2'' : (s4.gpr .r16).toNat = a 2 := by rw [r4.gpr _ (by decide)]; exact g2'
    have p3'' : (s4.gpr .r22).toNat = a 3 * 2 ^ 5 := by rw [r4.gpr _ (by decide)]; exact p3'
    have e24' : s4.gpr .r24 = BitVec.ofNat 64 19 := by
      rw [r4.gpr _ (by decide)]; exact BitVec.eq_of_toNat_eq e24
    have q := tn_shl g2'' 4 (by omega_using [b2]); have d := tn_shl g2'' 9 (by omega_using [b2])
    have n3 := tn_mul19 p3'' (by omega_using [b3])
    rw [← Nat.mul_assoc] at n3
    crunr [sqrP2, e24']
    exact ⟨q, d, n3, by rw [r4.gpr _ (by decide)]; exact n4, by rw [r4.gpr _ (by decide)]; exact g3',
      by rw [r4.gpr _ (by decide)]; exact g4'⟩
  refine WP.append (form_ok h2 sqr_writes.2.2.1 A4) fun s5 ⟨⟨q2, d2, n3, n4', g3'', g4'', m5⟩, r5, A5⟩ => ?_
  refine WP.append (terms_ok sqrT2 _ _ s5 (by decide) (by decide) A5 fun t ht => by
      simp only [sqrT2, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> rw [pv_def] <;> exact pv_lt (by omega_using [d2, b2])
        (by omega_using [q2, n3, n4', b2, b3, b4])) fun s6 ⟨A6, r6, m6⟩ => ?_
  -- `a3`'s
  have n3' : (s6.gpr .r22).toNat = 19 * a 3 * 2 ^ 5 := by rw [r6.gpr _ (by decide)]; exact n3
  have n4'' : (s6.gpr .r23).toNat = 19 * a 4 * 2 ^ 5 := by rw [r6.gpr _ (by decide)]; exact n4'
  have g3s : (s6.gpr .r17).toNat = a 3 := by rw [r6.gpr _ (by decide)]; exact g3''
  have g4s : (s6.gpr .r18).toNat = a 4 := by rw [r6.gpr _ (by decide)]; exact g4''
  have h3 : WP isa (.block [Instr.lsl .r17 .r17 8]) s6 fun s' =>
      (s'.gpr .r17).toNat = a 3 * 2 ^ 8 ∧ s'.mem = s6.mem := by
    have x := tn_shl g3s 8 (by omega_using [b3])
    crunr
    exact x
  refine WP.append (form_ok h3 sqr_writes.2.2.2.1 A6) fun s7 ⟨⟨x3, m7⟩, r7, A7⟩ => ?_
  have n3s7 : (s7.gpr .r22).toNat = 19 * a 3 * 2 ^ 5 := by rw [r7.gpr _ (by decide)]; exact n3'
  refine WP.append (terms_ok [(false, .r17, .r22, 1)] _ _ s7 (by decide) (by decide) A7 fun t ht => by
      rw [List.mem_singleton.mp ht, pv_def]
      exact pv_lt (by omega_using [x3, b3]) (by omega_using [n3s7, b3])) fun s8 ⟨A8, r8, m8⟩ => ?_
  have x3' : (s8.gpr .r17).toNat = a 3 * 2 ^ 8 := by rw [r8.gpr _ (by decide)]; exact x3
  have h4 : WP isa (.block [Instr.lsl .r17 .r17 1]) s8 fun s' =>
      (s'.gpr .r17).toNat = a 3 * 2 ^ 9 ∧ s'.mem = s8.mem := by
    have x := tn_shl x3' 1 (by omega_using [b3])
    rw [show a 3 * 2 ^ 8 * 2 ^ 1 = a 3 * 2 ^ 9 by omega_using []] at x
    crunr
    exact x
  refine WP.append (form_ok h4 sqr_writes.2.2.2.2.1 A8) fun s9 ⟨⟨d3, m9⟩, r9, A9⟩ => ?_
  have n4s9 : (s9.gpr .r23).toNat = 19 * a 4 * 2 ^ 5 := by
    rw [r9.gpr _ (by decide), r8.gpr _ (by decide), r7.gpr _ (by decide)]; exact n4''
  refine WP.append (terms_ok [(false, .r17, .r23, 2)] _ _ s9 (by decide) (by decide) A9 fun t ht => by
      rw [List.mem_singleton.mp ht, pv_def]
      exact pv_lt (by omega_using [d3, b3]) (by omega_using [n4s9, b4])) fun s10 ⟨A10, r10, m10⟩ => ?_
  -- `a4`'s
  have g4s10 : (s10.gpr .r18).toNat = a 4 := by
    rw [r10.gpr _ (by decide), r9.gpr _ (by decide), r8.gpr _ (by decide), r7.gpr _ (by decide)]; exact g4s
  have h5 : WP isa (.block [Instr.lsl .r18 .r18 8]) s10 fun s' =>
      (s'.gpr .r18).toNat = a 4 * 2 ^ 8 ∧ s'.mem = s10.mem := by
    have x := tn_shl g4s10 8 (by omega_using [b4])
    crunr
    exact x
  refine WP.append (form_ok h5 sqr_writes.2.2.2.2.2 A10) fun s11 ⟨⟨x4, m11⟩, r11, A11⟩ => ?_
  have n4s11 : (s11.gpr .r23).toNat = 19 * a 4 * 2 ^ 5 := by
    rw [r11.gpr _ (by decide), r10.gpr _ (by decide)]; exact n4s9
  refine WP.append (terms_ok [(false, .r18, .r23, 3)] _ _ s11 (by decide) (by decide) A11 fun t ht => by
      rw [List.mem_singleton.mp ht, pv_def]
      exact pv_lt (by omega_using [x4, b4]) (by omega_using [n4s11, b4])) fun s12 ⟨A12, r12, m12⟩ => ?_
  -- the reduction
  have hn : ∀ k < 5, accN [(false, Reg.r18, Reg.r23, 3)] (accN [(false, Reg.r17, Reg.r23, 2)]
      (accN [(false, Reg.r17, Reg.r22, 1)] (accN sqrT2 (accN sqrT1 (accN sqrT0 fun _ => 0))))) k = 3 := by
    decide +kernel
  have rAll : Rest coreRegs s s12 :=
    (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
    ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans ((r6.mono (by decide)).trans
    ((r7.mono (by decide)).trans ((r8.mono (by decide)).trans ((r9.mono (by decide)).trans
    ((r10.mono (by decide)).trans ((r11.mono (by decide)).trans (r12.mono (by decide))))))))))))
  have mAll : s12.mem = s.mem := by rw [m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1]
  refine WP.mono (tail_ok ho ho4 (hc.of_rest rAll (by decide))
    (fun k hk => A12.val k hk (by rw [hn k hk]; decide))
    (fun k hk => by have := A12.low k hk (by rw [hn k hk]; decide); rw [hn k hk] at this; omega_using [this])
    (fun k hk => by have := A12.bnd k hk (by rw [hn k hk]; decide); rw [hn k hk] at this; omega_using [this]))
    fun s13 ⟨r13, f13, t13, v13, l13⟩ => ⟨rAll.trans (r13.mono (by decide)), by rw [← mAll]; exact f13, t13, ?_, l13⟩
  rw [v13]
  have e : val5 a * val5 a = val5 (lim (a 0) (a 1) (a 2) (a 3) (a 4)) * val5 (lim (a 0) (a 1) (a 2) (a 3) (a 4)) := rfl
  rw [e, ← sqr_ident]
  simp only [val5, accC, stepC, sqrT0, sqrT1, sqrT2, pv_def, ↓reduceIte, Nat.reduceEqDiff, Nat.succ_ne_self,
    reduceCtorEq, Nat.zero_add]
  rw [prod_div d0 q0 rfl, prod_div2 d1 n4 rfl, prod_div2 d2 n3 rfl, prod_div2 d0 p1 rfl, prod_div2 d2 n4' rfl,
    prod_div x3 n3s7 rfl, prod_div2 d0 p2 rfl, prod_div d1 q1 rfl, prod_div2 d3 n4s9 rfl, prod_div2 d0 p3 rfl,
    prod_div2 d1 p2' rfl, prod_div x4 n4s11 rfl, prod_div2 d0 p4 rfl, prod_div2 d1 p3' rfl, prod_div d2 q2 rfl]

end

end VG.Proof.X25519.PPC64LE.Fe51
