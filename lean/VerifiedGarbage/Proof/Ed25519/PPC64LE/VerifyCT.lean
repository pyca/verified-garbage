module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Decode
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointScalar
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.X25519.PPC64LE.Field
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Decode
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointScalar
meta import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Packed
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarReduce
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyPoints
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Packed
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarReduce
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.X25519.PPC64LE.Field
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.TCB.PPC64LE.Target

/-! ### `Ed25519.PPC64LE.VerifyFn`, which this module and modules that import it used -/

section

/-! ### `Ed25519.PPC64LE.VerifyBody`, which only this module used -/

section

/-!
# Ed25519 on PPC64LE: the body of the verification

`S < L` (`verifyScalar_ok`), then `A` and `R` decoded by one loop of two
iterations into the tables at 7776 and 7904 (`decodeBoth_ok`, its invariant
`DecInv`), then the equation if both are points (`verifyDecode_ok`): in `r17`,
`verifyEquation` of the inputs (`verifyBody_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (decodeLE bytesAt)

/-- The equation, once `S < L`. -/
def eqResult (m : Mem) (pk sig ch : Addr) : Bool :=
  match Spec.Ed25519.decodePoint (bytesAt m pk 32), Spec.Ed25519.decodePoint (bytesAt m sig 32) with
  | some a, some r =>
    Spec.Ed25519.pointEqual
      (Spec.Ed25519.pointMul (decodeLE (bytesAt m (sig + BitVec.ofNat 64 32) 32)) Spec.Ed25519.basePoint)
      (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (decodeLE (bytesAt m ch 64)) a))
  | _, _ => false

theorem verifyEquation_eq (m : Mem) (pk sig ch : Addr) :
    Spec.Ed25519.verifyEquation (bytesAt m pk 32) (bytesAt m sig 64) (bytesAt m ch 64) =
      (decide (decodeLE (bytesAt m (sig + BitVec.ofNat 64 32) 32) < Spec.Ed25519.L) && eqResult m pk sig ch) := by
  have l32 : (bytesAt m pk 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  have l64 : (bytesAt m sig 64).length = 64 := by simp [Spec.Ed25519.bytesAt]
  have l64' : (bytesAt m ch 64).length = 64 := by simp [Spec.Ed25519.bytesAt]
  unfold Spec.Ed25519.verifyEquation eqResult
  rw [l32, l64, l64', Proof.Ed25519.signatureBytes_take, Proof.Ed25519.signatureBytes_drop]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  cases Spec.Ed25519.decodePoint (bytesAt m pk 32) <;> cases Spec.Ed25519.decodePoint (bytesAt m sig 32) <;> simp

section
variable {b pk sig ch : Addr}

/-- **`S < L`**: `r8` zero exactly when the signature's second half is below `L`. -/
theorem verifyScalar_ok {s : State} (h : VCtx b pk sig ch s) :
    WP isa (.block verifyScalar) s fun t =>
      Rest [.r5, .r7, .r8, .r14] s t ∧ Frame [FA b] s.mem t.mem ∧
      (t.gpr .r8 = 0 ↔ decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 32) 32) < Spec.Ed25519.L) := by
  have hS := SR_eq
  have hD := SD_eq
  rw [show verifyScalar = .addi .r14 .r30 32 :: (unpackField SR 0 ++ (.li .r8 1 :: pass .r6 SD scalarSubtractSrc))
    from rfl]
  refine wp_addi (by decide) (by decide) fun s1 u1 => ?_
  have hc1 : Ctx8 b s1 := h.ctx.of_rest (u1.rest (ws := [.r14]) (by decide)) (by decide)
  refine WP.append (unpackField_ok hc1.ctx (q := sig + BitVec.ofNat 64 32) (o := SR) (src := 0)
    (by rw [u1.gpr, h.r30]) (by decide) (by decide)
    (fun k hk => by
      rw [u1.rd, u1.wr, Offset.add_add]
      exact in_base (List.mem_append_left _ h.sigR) (by omega_arith) (by omega_arith))
    (by
      rw [BitVec.add_zero]
      exact (h.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide))).sub_right
        (Offset.sub_base b (by omega_arith))))
    fun s2 ⟨r2, f2, l2⟩ => ?_
  have hv : decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 32) 32) = V s2.mem b SR :=
    bytes_of_words fun j hj => by rw [l2 j hj, Nat.zero_add, ← u1.mem]
  refine wp_li (by decide) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc1.ctx.of_rest ((r2.mono (ws' := [.r7, .r8]) (by decide)).trans (u3.rest (by decide)))
    (by decide)
  refine WP.mono (subtract_ok hc3 u3.gpr) fun t ⟨r4, f4, l4, e8, _⟩ => ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((u3.rest (by decide)).trans (r4.mono (by decide))))
  · rw [← u1.mem]
    have fa : Frame [FA b] s1.mem s2.mem := f2.sub fun r hr => ⟨FA b, by simp, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_arith) (by omega_arith)⟩
    have fb : Frame [FA b] s2.mem t.mem := by
      rw [← u3.mem]
      exact f4.sub fun r hr => ⟨FA b, by simp, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_arith) (by omega_arith)⟩
    exact fa.trans fb
  · have hz : t.gpr .r8 = 0 ↔ (t.gpr .r8).toNat = 0 :=
      ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
    have hv3 : V s3.mem b SR = V s2.mem b SR := by rw [u3.mem]
    rw [hz, e8, hv, ← hv3]
    by_cases hL : Spec.Ed25519.L ≤ V s3.mem b SR
    · rw [ite_eq_left hL]; exact ⟨fun h => absurd h (by decide), fun h => absurd hL (by omega_arith)⟩
    · rw [ite_eq_right hL]; exact ⟨fun _ => by omega_arith, fun _ => rfl⟩

/-! ## Decoding `A` and `R` -/

def inPtr (pk sig : Addr) (k : Nat) : Addr := if k = 0 then pk else sig

/-- Whether the first `k` inputs decode to points. -/
def decOk (m : Mem) (pk sig : Addr) : Nat → Bool
  | 0 => true
  | k + 1 => decOk m pk sig k && (Spec.Ed25519.decodePoint (bytesAt m (inPtr pk sig k) 32)).isSome

/-- What the decoding loop writes. -/
abbrev decW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 SIGN, 8⟩, FA b, ⟨b + BitVec.ofNat 64 7776, 256⟩]

abbrev decR : List Reg := .r7 :: .r14 :: .r18 :: .r27 :: .r28 :: .r17 :: fclob

/-- After `k` decodings from `s0`. -/
structure DecInv (s0 : State) (b pk sig ch : Addr) (k : Nat) (t : State) : Prop where
  ctx : VCtx b pk sig ch t
  rest : Rest decR s0 t
  frame : Frame (decW b) s0.mem t.mem
  r27 : t.gpr .r27 = inPtr pk sig k
  r28 : t.gpr .r28 = BitVec.ofNat 64 (7776 + 128 * k)
  r18 : t.gpr .r18 = if decOk s0.mem pk sig k then 1 else 0
  tables : ∀ j < k, ∀ p, Spec.Ed25519.decodePoint (bytesAt s0.mem (inPtr pk sig j) 32) = some p →
    tableAt t.mem b (7776 + 128 * j) = p

theorem decW_sub : ∀ r ∈ decW b, Region.Sub r ⟨b, 8192⟩ := by
  intro r hr
  have hS : SIGN = 24 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.sub_base _ (by omega_arith)
  · exact Offset.sub_base _ (by omega_arith)
  · exact Offset.sub_base _ (by omega_arith)

theorem and_flag (x y : Bool) :
    (if x then (1 : BitVec 64) else 0) &&& (if y then 1 else 0) = if x && y then 1 else 0 := by
  cases x <;> cases y <;> rfl

/-- The decoding's result recorded: `r18`, the table entry, the next input. -/
theorem decodeNext_ok {s0 t u : State} {k : Nat} (hk : k < 2) (h : DecInv s0 b pk sig ch k t) {q : Addr}
    (hq : q = inPtr pk sig k) (hRt : Rest (.r14 :: .r17 :: fclob) t u)
    (hfu : Frame [⟨b + BitVec.ofNat 64 SIGN, 8⟩, FA b] t.mem u.mem) (hvu : VCtx b pk sig ch u)
    {o : Option Spec.Ed25519.Point} (ho : Spec.Ed25519.decodePoint (bytesAt s0.mem q 32) = o)
    (du : DecodeResult b o u) :
    WP isa (.block decodeNext) u fun w => DecInv s0 b pk sig ch (k + 1) w ∧
      w.gpr .r7 = BitVec.ofNat 64 (7776 + 128 * (k + 1)) - BitVec.ofNat 64 8032 := by
  have hS : SIGN = 24 := rfl
  unfold decodeNext
  simp only [List.cons_append, List.nil_append]
  refine wp_and fun u1' v1 => wp_add fun u2' v2 => ?_
  have hR2 : Rest [.r18, .r14] u u2' := (v1.rest (by decide)).trans (v2.rest (by decide))
  have e14' : u2'.gpr .r14 = b + BitVec.ofNat 64 (7776 + 128 * k) := by
    rw [v2.gpr, v1.other _ (by decide), hvu.ctx.r6, v1.other _ (by decide), hRt.gpr _ (by decide), h.r28]
  have hv2 : VCtx b pk sig ch u2' := hvu.of_rest hR2 (by decide)
  refine WP.append (pointToTable_ok hv2.ctx e14' (by omega_arith) (by omega_arith)) fun w ⟨rw', fw, tw⟩ => ?_
  refine wp_addi (by decide) (by decide) fun w1 x1 => wp_addi (by decide) (by decide) fun w2 x2 =>
    wp_subi (by decide) (by decide) fun w3 x3 => WP.block_nil ⟨?_, ?_⟩
  · have hRw : Rest decR u w3 := (hR2.mono (by decide)).trans ((rw'.mono (by decide)).trans
      ((x1.rest (by decide)).trans ((x2.rest (by decide)).trans (x3.rest (by decide)))))
    have hm3 : w3.mem = w.mem := by rw [x3.mem, x2.mem, x1.mem]
    have hmu : u2'.mem = u.mem := by rw [v2.mem, v1.mem]
    have e28 : w1.gpr .r28 = BitVec.ofNat 64 (7776 + 128 * k) := by
      rw [x1.other _ (by decide), rw'.gpr _ (by decide), hR2.gpr _ (by decide), hRt.gpr _ (by decide), h.r28]
    refine ⟨hvu.of_rest hRw (by decide), h.rest.trans ((hRt.mono (by decide)).trans hRw), ?_, ?_, ?_, ?_,
      fun j hj p hp => ?_⟩
    · have f1 : Frame (decW b) t.mem u.mem := hfu.mono (by simp)
      have f2 : Frame (decW b) u.mem w3.mem := by
        rw [hm3, ← hmu]
        exact fw.sub fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact ⟨⟨b + BitVec.ofNat 64 7776, 256⟩, by simp, Offset.sub b (by omega_arith) (by omega_arith)⟩
      exact h.frame.trans (f1.trans f2)
    · rw [x3.other _ (by decide), x2.other _ (by decide), x1.gpr, BitVec.add_zero, rw'.gpr _ (by decide),
        hR2.gpr _ (by decide), hvu.r30]
      unfold inPtr; rw [ite_eq_right (by omega_arith)]
    · rw [x3.other _ (by decide), x2.gpr, e28, BitVec.ofNat_add_ofNat]
      congr 1
    · rw [x3.other _ (by decide), x2.other _ (by decide), x1.other _ (by decide), rw'.gpr _ (by decide),
        v2.other _ (by decide), v1.gpr, hRt.gpr _ (by decide), h.r18]
      have e17 : u.gpr .r17 = if o.isSome then 1 else 0 := by
        cases o with
        | none => exact du
        | some p => exact du.1
      rw [e17, and_flag, decOk, ← hq, ho]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [hm3, tableAt_keep fw (fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
          hmu, tableAt_keep hfu (fun r hr => by
            have hS : SIGN = 24 := rfl
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
            · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith))]
        exact h.tables j hj p hp
      · rw [← hq, ho] at hp
        subst hp
        rw [hm3, tw, hmu]
        exact du.2
  · rw [x3.gpr, x2.gpr, x1.other _ (by decide), rw'.gpr _ (by decide), hR2.gpr _ (by decide),
      hRt.gpr _ (by decide), h.r28, BitVec.ofNat_add_ofNat]
    congr 2

/-- **One decoding**, of input `k`. -/
theorem decodeBody_ok {s0 t : State} {k : Nat} (hk : k < 2) (h : DecInv s0 b pk sig ch k t) :
    WP isa decodeBody t fun u => DecInv s0 b pk sig ch (k + 1) u ∧
      u.gpr .r7 = BitVec.ofNat 64 (7776 + 128 * (k + 1)) - BitVec.ofNat 64 8032 := by
  have hS : SIGN = 24 := rfl
  have h1 : offset 1 = 96 := rfl
  unfold decodeBody
  refine WP.seq (wp_addi (by decide) (by decide) fun t1 u1 => WP.block_nil ?_)
  have hv1 : VCtx b pk sig ch t1 := h.ctx.of_rest (u1.rest (ws := [.r14]) (by decide)) (by decide)
  obtain ⟨q, hq⟩ : ∃ q, q = inPtr pk sig k := ⟨_, rfl⟩
  have e14 : t1.gpr .r14 = q := by rw [u1.gpr, BitVec.add_zero, h.r27, hq]
  have hqR : (∀ j < 8, InRegions (t1.rd ++ t1.wr) (q + BitVec.ofNat 64 (0 + 4 * j)) 4) ∧
      (⟨q, 32⟩ : Region).Disjoint ⟨b, 8192⟩ := by
    rw [hq]; unfold inPtr
    by_cases h0 : k = 0
    · rw [ite_eq_left h0]
      exact ⟨fun j hj => in_base (List.mem_append_left _ hv1.pkR) (by omega_arith) (by omega_arith), hv1.pkD⟩
    · rw [ite_eq_right h0]
      exact ⟨fun j hj => in_base (List.mem_append_left _ hv1.sigR) (by omega_arith) (by omega_arith),
        hv1.sigD.sub_left (Region.sub_prefix (by decide))⟩
  obtain ⟨hr4, hdq⟩ := hqR
  have hb : bytesAt t1.mem q 32 = bytesAt s0.mem q 32 := by
    rw [u1.mem]; exact bytesAt_ws h.frame decW_sub hdq (by decide)
  refine WP.seq (WP.mono (pointDecode_ok hv1.ctx e14 hr4 (by
    rw [BitVec.add_zero]; exact hdq.sub_right (Offset.sub_base b (by omega_arith)))) fun u ⟨ku, o, ho, du⟩ =>
      decodeNext_ok hk h hq ((u1.rest (by decide)).trans (ku.rest.mono (by decide)))
        (by rw [← u1.mem]; exact ku.frame) (hv1.of_rest ku.rest (by decide)) (by rw [← hb]; exact ho) du)

theorem decodeStart_ok {s : State} (h : VCtx b pk sig ch s) :
    WP isa (.block decodeStart) s (DecInv s b pk sig ch 0) := by
  unfold decodeStart
  refine wp_addi (by decide) (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 =>
    wp_li (by decide) fun s3 u3 => WP.block_nil ?_
  have hr3 : Rest [.r27, .r28, .r18] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  exact ⟨h.of_rest hr3 (by decide), hr3.mono (by decide), by rw [u3.mem, u2.mem, u1.mem]; exact Frame.refl _ _,
    by rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, BitVec.add_zero, h.r29]; rfl,
    by rw [u3.other _ (by decide), u2.gpr], by rw [u3.gpr]; rfl, fun j hj => absurd hj (by omega_arith)⟩

/-- **`A` and `R` decoded**, into the tables at 7776 and 7904. -/
theorem decodeBoth_ok {s : State} (h : VCtx b pk sig ch s) : WP isa decodeBoth s (DecInv s b pk sig ch 2) := by
  unfold decodeBoth
  refine WP.seq (WP.mono (decodeStart_ok h) fun s3 hd0 => ?_)
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ 2 ∧ DecInv s b pk sig ch (2 - n) t) ?_ 2 s3
    ⟨by decide, Nat.le_refl _, show DecInv s b pk sig ch (2 - 2) s3 from hd0⟩
  rintro n t ⟨h1, h2, hi⟩
  refine WP.mono (decodeBody_ok (k := 2 - n) (by omega_arith) hi) fun u ⟨hu, e7⟩ => ?_
  rw [eval_nonzero, e7]
  rcases (by omega_arith : n = 1 ∨ n = 2) with rfl | rfl
  · exact .inl ⟨by decide, hu⟩
  · exact .inr ⟨by decide, 1, by decide, by decide, by decide, hu⟩

/-- What the verification writes. -/
abbrev verW (b : Addr) : List Region :=
  ⟨b + BitVec.ofNat 64 SIGN, 8⟩ :: ⟨b + BitVec.ofNat 64 7776, 256⟩ :: sideW b 8032

abbrev verR : List Reg := .r18 :: .r27 :: .r28 :: .r17 :: sideR

theorem eqResult_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩)
    {s : State} (h : VCtx b pk sig ch s) : eqResult m' pk sig ch = eqResult m pk sig ch := by
  unfold eqResult
  rw [bytesAt_ws hf hs h.pkD (by decide), bytesAt_ws hf hs (h.sigD.sub_left (Region.sub_prefix (by decide)))
      (by decide),
    bytesAt_ws hf hs (h.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide))) (by decide),
    bytesAt_ws hf hs h.chD (by decide)]

/-- **The equation, if `A` and `R` are points.** -/
theorem verifyDecode_ok (hR : RhsOk) {s : State} (h : VCtx b pk sig ch s) (hB : BStat b (s.syms bSym) s) :
    WP isa verifyDecode s fun t => Rest verR s t ∧ Frame (verW b) s.mem t.mem ∧
      t.gpr .r17 = if eqResult s.mem pk sig ch then 1 else 0 := by
  unfold verifyDecode
  refine WP.seq (WP.mono_syms (decodeBoth_ok h) fun s1 h1 sy1 => ?_)
  have hf1 : Frame (verW b) s.mem s1.mem := h1.frame.mono (by simp)
  have he1 : eqResult s1.mem pk sig ch = eqResult s.mem pk sig ch := eqResult_frame h1.frame decW_sub h
  have hB1 : BStat b (s1.syms bSym) s1 := by
    rw [sy1]; exact hB.of_frame h1.rest.rd h1.frame decW_sub
  refine WP.ite (s1.gpr .r18 != 0) (eval_nonzero s1 .r18) (fun hb => ?_) (fun hb => ?_)
  · have hok : decOk s.mem pk sig 2 = true := by
      rw [h1.r18] at hb
      revert hb; cases decOk s.mem pk sig 2 <;> decide
    simp only [decOk, Bool.true_and, Bool.and_eq_true] at hok
    obtain ⟨ha, hr⟩ := hok
    obtain ⟨a, ea⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨r, er⟩ := Option.isSome_iff_exists.mp hr
    have ta : tableAt s1.mem b 7776 = a := h1.tables 0 (by decide) a ea
    have tr : tableAt s1.mem b 7904 = r := h1.tables 1 (by decide) r er
    unfold verifyEquationPoints
    refine WP.mono (hR h1.ctx hB1 (by rw [ta]; exact ea) (by rw [tr]; exact er)) fun t ⟨rt, ft, et⟩ =>
      ⟨?_, ?_, ?_⟩
    · exact (h1.rest.mono (by decide)).trans (rt.mono (by decide))
    · exact hf1.trans (ft.mono (by simp))
    · rw [et, ta, tr, bytesAt_ws h1.frame decW_sub h.chD (by decide),
        bytesAt_ws h1.frame decW_sub (h.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide)))
          (by decide)]
      unfold eqResult
      simp only [inPtr, ite_eq_left] at ea er
      rw [show (if (1 : Nat) = 0 then pk else sig) = sig from rfl] at er
      rw [ea, er]
  · have hno : decOk s.mem pk sig 2 = false := by
      rw [h1.r18] at hb
      revert hb; cases decOk s.mem pk sig 2 <;> decide
    refine WP.mono (recoverInvalid_ok (b := b) s1) fun t ⟨kt, mt, dt⟩ => ⟨?_, ?_, ?_⟩
    · exact (h1.rest.mono (by decide)).trans (kt.rest.mono (by decide))
    · rw [mt]; exact hf1
    · rw [show t.gpr .r17 = 0 from dt]
      simp only [decOk, Bool.true_and, Bool.and_eq_false_iff] at hno
      have hf : eqResult s.mem pk sig ch = false := by
        unfold eqResult
        simp only [inPtr, ↓reduceIte, Nat.one_ne_zero] at hno
        revert hno
        cases Spec.Ed25519.decodePoint (bytesAt s.mem pk 32) <;>
          cases Spec.Ed25519.decodePoint (bytesAt s.mem sig 32) <;> simp
      rw [hf]; rfl

/-- **The verification's body**: `verifyEquation` of the inputs, in `r17`. -/
theorem verifyBody_ok (hR : RhsOk) {s : State} (h : VCtx b pk sig ch s) (hB : BStat b (s.syms bSym) s) :
    WP isa verifyBody s fun t => Rest verR s t ∧ Frame (verW b) s.mem t.mem ∧
      t.gpr .r17 = if Spec.Ed25519.verifyEquation (bytesAt s.mem pk 32) (bytesAt s.mem sig 64)
        (bytesAt s.mem ch 64) then 1 else 0 := by
  unfold verifyBody
  refine WP.seq (WP.mono_syms (verifyScalar_ok h) fun s1 ⟨r1, f1, h8⟩ sy1 => ?_)
  rw [verifyEquation_eq]
  have hv1 : VCtx b pk sig ch s1 := h.of_rest r1 (by decide)
  have hF : ∀ r ∈ [FA b], r ∈ verW b := by simp
  refine WP.ite (s1.gpr .r8 == 0) (eval_zero s1 .r8) (fun hz => ?_) (fun hz => ?_)
  · have hlt := h8.mp (beq_iff_eq.mp hz)
    refine WP.seq (WP.mono_syms (initFields_ok hv1.ctx.ctx) fun s2 ⟨r2, f2⟩ sy2 => ?_)
    have hB2 : BStat b (s2.syms bSym) s2 := by
      rw [sy2, sy1]
      exact hB.of_frame (by rw [r2.rd, r1.rd]) (f1.trans f2) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_arith)
    refine WP.mono (verifyDecode_ok hR (hv1.of_rest r2 (by decide)) hB2) fun t ⟨rt, ft, et⟩ => ⟨?_, ?_, ?_⟩
    · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans rt)
    · exact (f1.mono hF).trans ((f2.mono hF).trans ft)
    · rw [et, eqResult_frame (f1.trans f2) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_arith)) h, decide_eq_true hlt, Bool.true_and]
  · have hge : ¬ decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 32) 32) < Spec.Ed25519.L :=
      fun hl => absurd (beq_iff_eq.mpr (h8.mpr hl)) (by simpa using hz)
    refine WP.mono (recoverInvalid_ok (b := b) s1) fun t ⟨kt, mt, dt⟩ => ⟨?_, ?_, ?_⟩
    · exact (r1.mono (by decide)).trans (kt.rest.mono (by decide))
    · rw [mt]; exact f1.mono hF
    · rw [show t.gpr .r17 = 0 from dt, decide_eq_false hge, Bool.false_and]; rfl

end

end VG.Proof.Ed25519.PPC64LE

end

end


/-!
# `vg_ed25519_verify_equation` on PPC64LE

The nonvolatile registers saved at `SAVE` and `lr` at `LRS` of `scratch`
(`r6`), the pointers moved to `r29`–`r31`, the body (`verifyBody_ok`, given
the windows' proof, `RhsOk`), and its result returned in `r3` (`verify_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (decodeLE bytesAt)

/-- The precondition, by register: `pk` in `r3`, the signature in `r4`, the challenge in `r5` and
`scratch` in `r6`; the static of `-[1]B … -[15]B` at `bSym`. -/
structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r4, 64⟩, ⟨s.gpr .r5, 64⟩, ⟨s.syms bSym, 1920⟩]
  wr : s.wr = [⟨s.gpr .r6, 8192⟩]
  pk_ws : (⟨s.gpr .r3, 32⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  sig_ws : (⟨s.gpr .r4, 64⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  ch_ws : (⟨s.gpr .r5, 64⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  /-- The static of `-[1]B … -[15]B`. -/
  bs : BStat (s.gpr .r6) (s.syms bSym) s

/-- The regions the verification writes are clear of the saved registers'. -/
theorem verW_saves {B : Addr} (lo n : Nat) (h1 : 1024 ≤ lo) (h2 : lo + n ≤ 1632) :
    ∀ r ∈ verW B, Region.Disjoint ⟨B + BitVec.ofNat 64 lo, n⟩ r := by
  intro r hr
  have hS : SIGN = 24 := rfl
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  exact mulW_saves lo n h1 h2 r hr

/-- **The setup**: the registers saved, `lr` saved, the pointers in `r29`–`r31`. -/
theorem verifySetup_ok {s : State} (hp : VerifyPre s) :
    WP isa (.block verifySetup) s fun t =>
      VCtx (s.gpr .r6) (s.gpr .r3) (s.gpr .r4) (s.gpr .r5) t ∧ Rest [.r7, .r29, .r30, .r31] s t ∧
      t.lr = s.lr ∧ Frame [⟨s.gpr .r6, 8192⟩] s.mem t.mem ∧ Spill.Saved (s.gpr .r6) s.gpr saveList t.mem ∧
      ∃ g : Reg → BitVec 64, g .r7 = s.lr ∧ Spill.Saved (s.gpr .r6) g [(.r7, LRS)] t.mem := by
  have hV := SAVE_eq
  have hL := LRS_eq
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r6 := ⟨_, rfl⟩
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  unfold verifySetup
  rw [scalarSave_eq]
  have hsin : ∀ p ∈ saveList, InRegions s.wr (s.gpr .r6 + BitVec.ofNat 64 p.2) 8 := fun p hpl => by
    have := saveList_in p hpl
    rw [← hb]; exact in_base hws (by omega_arith) (by omega_arith)
  refine Spill.save_ok (b := .r6) (by decide) saveList_fits hsin ?_
  generalize hs1 : ({ s with mem := Spill.saveMem s.mem (s.gpr .r6) s.gpr saveList } : State) = s1
  have hsv : Spill.Saved b s.gpr saveList s1.mem := by rw [← hs1, hb]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf1 : Frame [⟨b, 8192⟩] s.mem s1.mem := by
    rw [← hs1, hb]
    exact Spill.saveMem_frame_base (fun p hpl => by have := saveList_in p hpl; omega_arith) (by decide) _ _ _
  have hg1 : s1.gpr = s.gpr := by rw [← hs1]
  have hrd1 : s1.rd = s.rd := by rw [← hs1]
  have hwr1 : s1.wr = s.wr := by rw [← hs1]
  have hlr1 : s1.lr = s.lr := by rw [← hs1]
  have hsp1 : s1.sp = s.sp := by rw [← hs1]
  refine wp_addiL (by decide) (by decide) fun s2 u2 l2 => wp_addiL (by decide) (by decide) fun s3 u3 l3 =>
    wp_addiL (by decide) (by decide) fun s3' u3' l3' => wp_mflr fun s4 u4 l4 => ?_
  have hr4 : Rest [.r7, .r29, .r30, .r31] s1 s4 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans ((u3'.rest (by decide)).trans (u4.rest (by decide))))
  have e6 : s4.gpr .r6 = b := by rw [hr4.gpr _ (by decide), hg1, hb]
  have e7 : s4.gpr .r7 = s.lr := by rw [u4.gpr, l3', l3, l2, hlr1]
  -- The link register's slot.
  rw [← List.append_nil [Instr.store .d .r7 .r6 LRS]]
  refine Spill.save_ok (b := .r6) (l := [(.r7, LRS)]) (rest := []) (by decide) (by decide)
    (fun p hpl => by
      rw [List.mem_singleton.mp hpl, e6, hr4.wr, hwr1]; exact in_base hws (by omega_arith) (by omega_arith)) ?_
  generalize hs5 : ({ s4 with mem := Spill.saveMem s4.mem (s4.gpr .r6) s4.gpr [(.r7, LRS)] } : State) = s5
  have hsvL : Spill.Saved b s4.gpr [(.r7, LRS)] s5.mem := by
    rw [← hs5, ← e6]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf5 : Frame [⟨b + BitVec.ofNat 64 LRS, 8⟩] s4.mem s5.mem := by
    rw [← hs5, e6]
    exact Spill.saveMem_frame (lo := LRS) (n := 8) (fun p hpl => by rw [List.mem_singleton.mp hpl]; omega_arith)
      (by decide) _ _ _
  have hg5 : s5.gpr = s4.gpr := by rw [← hs5]
  have hR5 : Rest [.r7, .r29, .r30, .r31] s s5 := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [hg5, hr4.gpr _ hr, hg1]
    · rw [← hs5]; simp only []; rw [hr4.rd, hrd1]
    · rw [← hs5]; simp only []; rw [hr4.wr, hwr1]
    · rw [← hs5]; simp only []; rw [hr4.sp, hsp1]
  have hm4 : s4.mem = s1.mem := by rw [u4.mem, u3'.mem, u3.mem, u2.mem]
  have hF5 : Frame [⟨b, 8192⟩] s.mem s5.mem :=
    hf1.trans (by rw [← hm4]; exact hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base b (by omega_arith)⟩)
  have hv5 : VCtx b (s.gpr .r3) (s.gpr .r4) (s.gpr .r5) s5 := {
    ctx := ⟨by rw [hR5.gpr _ (by decide), hb], by rw [hR5.wr]; exact hws⟩
    r29 := by rw [hg5, u4.other _ (by decide), u3'.other _ (by decide), u3.other _ (by decide), u2.gpr, hg1,
      BitVec.add_zero]
    r30 := by rw [hg5, u4.other _ (by decide), u3'.other _ (by decide), u3.gpr, u2.other _ (by decide), hg1,
      BitVec.add_zero]
    r31 := by rw [hg5, u4.other _ (by decide), u3'.gpr, u3.other _ (by decide), u2.other _ (by decide), hg1,
      BitVec.add_zero]
    pkR := by rw [hR5.rd, hp.rd]; simp
    sigR := by rw [hR5.rd, hp.rd]; simp
    chR := by rw [hR5.rd, hp.rd]; simp
    pkD := hb ▸ hp.pk_ws
    sigD := hb ▸ hp.sig_ws
    chD := hb ▸ hp.ch_ws }
  refine WP.block_nil ⟨hb ▸ hv5, hR5, by rw [← hs5]; simp only []; rw [l4, l3', l3, l2, hlr1], hb ▸ hF5,
    hb ▸ ((hm4 ▸ hsv).frame_in (lo := SAVE) (n := 96) saveList_in hf5 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
    s4.gpr, e7, hb ▸ hsvL⟩

theorem verify_ok (hR : RhsOk) {s : State} (hp : VerifyPre s) :
    WP isa Impl.Ed25519.PPC64LE.verifyEquation s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      t.gpr .r3 = if Spec.Ed25519.verifyEquation (bytesAt s.mem (s.gpr .r3) 32) (bytesAt s.mem (s.gpr .r4) 64)
        (bytesAt s.mem (s.gpr .r5) 64) then 1 else 0 := by
  have hV := SAVE_eq
  have hL := LRS_eq
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r6 := ⟨_, rfl⟩
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  unfold Impl.Ed25519.PPC64LE.verifyEquation
  refine WP.seq (WP.mono_syms (verifySetup_ok hp) fun s5 ⟨hv5, hR5, _, hF5, hsv, g, hg, hsvL⟩ sy5 => ?_)
  rw [← hb] at hv5 hF5 hsv hsvL
  have hsub : ∀ r ∈ [(⟨b, 8192⟩ : Region)], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact fun _ h => h
  have hbytes : Spec.Ed25519.verifyEquation (bytesAt s5.mem (s.gpr .r3) 32) (bytesAt s5.mem (s.gpr .r4) 64)
      (bytesAt s5.mem (s.gpr .r5) 64) = Spec.Ed25519.verifyEquation (bytesAt s.mem (s.gpr .r3) 32)
        (bytesAt s.mem (s.gpr .r4) 64) (bytesAt s.mem (s.gpr .r5) 64) := by
    rw [bytesAt_ws hF5 hsub hv5.pkD (by decide), bytesAt_ws hF5 hsub hv5.sigD (by decide),
      bytesAt_ws hF5 hsub hv5.chD (by decide)]
  have hB5 : BStat b (s5.syms bSym) s5 := by
    rw [sy5]
    exact (hb ▸ hp.bs).of_frame hR5.rd hF5 hsub
  refine WP.seq (WP.mono (verifyBody_ok hR hv5 hB5) fun s7 ⟨r7, f7, e17⟩ => ?_)
  rw [hbytes] at e17
  -- The link register restored, the result, and the registers.
  unfold verifyFinish
  rw [scalarRestore_eq, show ([.load .d .r7 .r6 LRS, .mtlr .r7, .addi .r3 .r17 0] : List Instr) =
    Spill.restoreCode .r6 [(.r7, LRS)] ++ [.mtlr .r7, .addi .r3 .r17 0] from rfl]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hsvL7 : Spill.Saved b g [(.r7, LRS)] s7.mem :=
    hsvL.frame_in (lo := LRS) (n := 8) (fun p hpl => by rw [List.mem_singleton.mp hpl]; omega_arith) f7
      (verW_saves LRS 8 (by omega_arith) (by omega_arith))
  have hc7 : Ctx8 b s7 := hv5.ctx.of_rest r7 (by decide)
  refine Spill.restore_ok (b := .r6) (B := b) (by decide) hc7.r6 (by decide) (by decide)
    (fun p hpl => by rw [List.mem_singleton.mp hpl]; exact hc7.inR (by omega_arith)) hsvL7 fun s8 h8 => ?_
  refine wp_mtlr ?_
  generalize hu : ({ s8 with lr := s8.gpr .r7 } : State) = u
  have hlu : u.lr = s.lr := by rw [← hu]; simp only []; rw [h8.gpr _ (List.mem_singleton_self _)]; exact hg
  have hgu : u.gpr = s8.gpr := by rw [← hu]
  have hmu : u.mem = s7.mem := by rw [← hu]; exact h8.mem
  have hrdu : u.rd = s.rd := by rw [← hu]; simp only []; rw [h8.rd, r7.rd, hR5.rd]
  have hwru : u.wr = s.wr := by rw [← hu]; simp only []; rw [h8.wr, r7.wr, hR5.wr]
  have hspu : u.sp = s.sp := by rw [← hu]; simp only []; rw [h8.sp, r7.sp, hR5.sp]
  refine wp_addiL (by decide) (by decide) fun v uv lv => ?_
  have hsv7 : Spill.Saved b s.gpr saveList v.mem := by
    rw [uv.mem, hmu]
    exact hsv.frame_in (lo := SAVE) (n := 96) saveList_in f7 (verW_saves SAVE 96 (by omega_arith) (by omega_arith))
  have e6v : v.gpr .r6 = b := by rw [uv.other _ (by decide), hgu, h8.other _ (by decide), hc7.r6]
  refine Spill.restore_ok (b := .r6) (B := b) (by decide) e6v saveList_fits saveList_restorable
    (fun p hpl => by
      have := saveList_in p hpl
      rw [uv.rd, uv.wr, hrdu, hwru]
      exact in_base (List.mem_append_right _ hws) (by omega_arith) (by omega_arith)) hsv7 fun t ht => WP.block_nil
      ⟨fun r hr => ?_, by rw [ht.sp, uv.sp, hspu], by rw [ht.lr, lv, hlu], ?_⟩
  · by_cases hm : r ∈ savedRegs
    · rw [← saveList_regs] at hm
      exact ht.gpr_of (.inl hm)
    · rw [← saveList_regs] at hm
      rw [ht.other _ hm, uv.other _ (by revert hr; cases r <;> decide), hgu,
        h8.other _ (by revert hr; cases r <;> decide), r7.gpr _ (by revert hr hm; cases r <;> decide),
        hR5.gpr _ (by revert hr hm; cases r <;> decide)]
  · rw [ht.other _ (by decide), uv.gpr, hgu, h8.other _ (by decide), BitVec.add_zero, e17]

end VG.Proof.Ed25519.PPC64LE

end

end

/-! ### `Ed25519.PPC64LE.DecodeCT`, which this module and modules that import it used -/

section

/-!
# Ed25519 on PPC64LE: a decoding leaks only its encoding

Two runs of `pointDecode` on the same encoding, with the same working space
and stack pointer, leak the same trace (`pointDecode_ct`). The taint analysis
(`taint_decide`) checks each piece between the branches: memory is secret to
it, so the branches on `r5` are related by correctness instead: in both runs
`r5` is zero exactly when the same fact about the encoding holds (`RelCT.ite`).
Each relation says that both runs satisfy the same predicate of public values
(`Both`), as ARMv7's proofs do.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P Fe)
open VG.Spec.Ed25519 (decodeLE bytesAt)
open VG.Proof.Ed25519 (rootU rootV rootX)

/-- Both runs satisfy `A`. -/
abbrev Both (A : State → Prop) (s₁ s₂ : State) : Prop := A s₁ ∧ A s₂

theorem ctBoth {A B : State → Prop} {c : Prog isa} (h : RelCT isa (Both A) c fun _ _ => True)
    (hw : ∀ s, A s → WP isa c s B) : RelCT isa (Both A) c (Both B) :=
  (h.wp (F₁ := B) (F₂ := B) fun _ _ hp => ⟨hw _ hp.1, hw _ hp.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Code the taint analysis checks, with the registers of `rs` and `sp` agreeing. -/
theorem ctRegs (rs : List Reg) {A : State → Prop} {c : Prog isa}
    (hr : ∀ s₁ s₂, A s₁ → A s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {hc : Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa (Both A) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ hp => ⟨(hr _ _ hp.1 hp.2).1, fun r h => (hr _ _ hp.1 hp.2).2 r (by simpa using h)⟩) h

theorem eval_zero_agree {s₁ s₂ : State} {r : Reg} {p : Prop} (h₁ : s₁.gpr r = 0 ↔ p) (h₂ : s₂.gpr r = 0 ↔ p) :
    isa.eval (.zero .d r) s₁ = isa.eval (.zero .d r) s₂ := by
  rw [eval_zero, eval_zero]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact h₁.trans h₂.symm

/-- The working space at `r6` and the stack pointer. -/
def Pin (b sp : Addr) (s : State) : Prop := Ctx8 b s ∧ s.sp = sp

theorem Pin.regs {b sp : Addr} {s₁ s₂ : State} (h₁ : Pin b sp s₁) (h₂ : Pin b sp s₂) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r6], s₁.gpr r = s₂.gpr r :=
  ⟨h₁.2.trans h₂.2.symm, fun r hr => by rw [List.mem_singleton.mp hr, h₁.1.r6, h₂.1.r6]⟩

theorem Pin.of_rest {b sp : Addr} {s t : State} {R : List Reg} (h : Pin b sp s) (hr : Rest R s t)
    (h6 : Reg.r6 ∉ R) : Pin b sp t :=
  ⟨h.1.of_rest hr h6, by rw [hr.sp, h.2]⟩

section
variable {b sp : Addr}

theorem recoverInvalid_ct : RelCT isa (Both (Pin b sp)) recoverInvalid fun _ _ => True :=
  ctRegs [.r6] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)

/-- Before the sign is applied: `x` in slot 0, the sign at `SIGN`. -/
def AdjPre (b sp : Addr) (x : Fe) (sg : Bool) (s : State) : Prop :=
  Pin b sp s ∧ env s.mem b 0 = x ∧ SignAt b sg s.mem

theorem recoverAdjust_ct (x : Fe) (sg : Bool) :
    RelCT isa (Both (AdjPre b sp x sg)) recoverAdjustSign fun _ _ => True := by
  unfold recoverAdjustSign
  have h1 := ctBoth (ctRegs [.r6] (A := AdjPre b sp x sg) (c := .block (freeze 0 ++ recoverParity))
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
    (B := fun t => Pin b sp t ∧ (t.gpr .r5 = 0 ↔ ((x.val % 2 == 1) == sg) = true)) fun s h =>
      WP.mono (adjParity_ok h.1.1 h.2.2) fun t ⟨k, _, e⟩ => ⟨h.1.of_rest k.rest (by decide), by rw [← h.2.1]; exact e⟩
  refine RelCT.seq h1 (RelCT.seq (Q := fun _ _ => True) (R := Both (Pin b sp))
    (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_) ?_)
  · exact RelCT.block_nil fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩
  · exact (ctBoth (ctRegs [.r6] (A := Pin b sp) (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide))
      fun s h => WP.mono (fieldCode_ok _ h.1.ctx) fun t ⟨k, _⟩ => h.of_rest k.rest (by decide)).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact ctRegs [.r6] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)

theorem recoverSign_ct (x : Fe) (sg : Bool) :
    RelCT isa (Both (AdjPre b sp x sg)) recoverSign fun _ _ => True := by
  unfold recoverSign
  have h1 := ctBoth (ctRegs [.r6] (A := AdjPre b sp x sg) (c := fieldZero 0)
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
    (B := fun t => AdjPre b sp x sg t ∧ (t.gpr .r5 = 0 ↔ x = 0)) fun s h =>
      WP.mono (fieldZero_ok h.1.1.ctx 0) fun t ⟨r, f, e⟩ =>
        ⟨⟨h.1.of_rest r (by decide), by rw [env_FR f, h.2.1], h.2.2.frame (frame_FR f)⟩,
          by rw [e, ← h.2.1, Fin.ext_iff]; exact Iff.rfl⟩
  refine RelCT.seq h1 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · unfold signTest
    have h2 := ctBoth (ctRegs [.r6] (A := AdjPre b sp x sg) (c := .block [.load .d .r5 .r6 SIGN])
      (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
      (B := fun t => AdjPre b sp x sg t ∧ t.gpr .r5 = BitVec.ofNat 64 sg.toNat) fun s h =>
        wp_ldd (a := b + BitVec.ofNat 64 SIGN) (by decide) (by decide) (by rw [h.1.1.r6])
          (h.1.1.ctx.inR (by decide)) fun t u => WP.block_nil
            ⟨⟨h.1.of_rest (u.rest (ws := [.r5]) (by decide)) (by decide), by rw [u.mem]; exact h.2.1,
              by rw [u.mem]; exact h.2.2⟩, by rw [u.gpr]; exact h.2.2⟩
    refine RelCT.seq (h2.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
      (RelCT.ite (fun _ _ h => by rw [eval_nonzero, eval_nonzero, h.1.2, h.2.2]) ?_ ?_)
    · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h
    · exact (recoverAdjust_ct x sg).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact (recoverAdjust_ct x sg).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h

/-- Before the candidate: `y` in slot 1, the sign at `SIGN`. -/
def RPPre (b sp : Addr) (y : Fe) (sg : Bool) (s : State) : Prop :=
  Pin b sp s ∧ env s.mem b 1 = y ∧ SignAt b sg s.mem

theorem recoverPoint_ct (y : Fe) (sg : Bool) :
    RelCT isa (Both (RPPre b sp y sg)) recoverPoint fun _ _ => True := by
  unfold recoverPoint
  -- The candidate, and `v x²` against `u` and `-u`.
  let C (t : State) : Prop := Pin b sp t ∧ SignAt b sg t.mem ∧ env t.mem b 0 = rootX y ∧
    env t.mem b 11 = rootV y * rootX y * rootX y ∧ env t.mem b 6 = rootU y ∧ env t.mem b 12 = 0 - rootU y
  have h1 := ctBoth (ctRegs [.r6] (A := RPPre b sp y sg) (c := recoverCandidate)
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide)) (B := C) fun s h =>
      WP.mono (recoverCandidate_ok h.1.1) fun t ⟨k, x0, _, x6, _, x11, x12⟩ =>
        ⟨h.1.of_rest k.rest (by decide), h.2.2.frame k.frame, by rw [x0, h.2.1], by rw [x11, h.2.1],
          by rw [x6, h.2.1], by rw [x12, h.2.1]⟩
  have hC (t : State) (h : C t) {u : State} (k : Keep b t u) {c : Slot}
      (e : env u.mem b = evalOps [.sub 21 11 c] (env t.mem b)) : C u :=
    ⟨h.1.of_rest k.rest (by decide), h.2.1.frame k.frame, by rw [e]; exact h.2.2.1, by rw [e]; exact h.2.2.2.1,
      by rw [e]; exact h.2.2.2.2.1, by rw [e]; exact h.2.2.2.2.2⟩
  have h6 := ctBoth (ctRegs [.r6] (A := C) (c := fieldEqual 11 6) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => C t ∧ (t.gpr .r5 = 0 ↔ rootV y * rootX y * rootX y = rootU y)) fun s h =>
      WP.mono (fieldEqual_ok h.1.1.ctx 11 6) fun t ⟨k, e, z⟩ =>
        ⟨hC s h k e, by rw [z, h.2.2.2.1, h.2.2.2.2.1]⟩
  have h12 := ctBoth (ctRegs [.r6] (A := C) (c := fieldEqual 11 12) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => C t ∧ (t.gpr .r5 = 0 ↔ rootV y * rootX y * rootX y = 0 - rootU y))
      fun s h => WP.mono (fieldEqual_ok h.1.1.ctx 11 12) fun t ⟨k, e, z⟩ =>
        ⟨hC s h k e, by rw [z, h.2.2.2.1, h.2.2.2.2.2]⟩
  have hA (t : State) (h : C t) : AdjPre b sp (rootX y) sg t := ⟨h.1, h.2.2.1, h.2.1⟩
  refine RelCT.seq h1 (RelCT.seq h6 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_))
  · exact (recoverSign_ct (rootX y) sg).mono (fun _ _ h => ⟨hA _ h.1.1.1, hA _ h.1.2.1⟩) fun _ _ h => h
  refine RelCT.seq (h12.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
    (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · have hF := ctBoth (ctRegs [.r6] (A := C) (c := fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18])
      (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
      (B := AdjPre b sp (rootX y * Spec.Ed25519.sqrtM1) sg) fun s h =>
        WP.mono (fieldCode_ok _ h.1.1.ctx) fun t ⟨k, e⟩ =>
          ⟨h.1.of_rest k.rest (by decide), by rw [e, ← h.2.2.1]; rfl, h.2.1.frame k.frame⟩
    exact RelCT.seq (hF.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h) (recoverSign_ct _ sg)
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h

/-- Before a decoding: the encoding `bs` at `r14`. -/
def DecPre (b sp q : Addr) (bs : List Byte) (s : State) : Prop :=
  Pin b sp s ∧ s.gpr .r14 = q ∧ (∀ k < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (0 + 4 * k)) 4) ∧
    (⟨q + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 (offset 1), 32⟩ ∧ bytesAt s.mem q 32 = bs

/-- **A decoding leaks only its encoding.** -/
theorem pointDecode_ct (q : Addr) (bs : List Byte) :
    RelCT isa (Both (DecPre b sp q bs)) pointDecode fun _ _ => True := by
  unfold pointDecode
  have h1 := ctBoth (ctRegs [.r6, .r14] (A := DecPre b sp q bs) (c := pointDecodeLoad)
    (fun _ _ h₁ h₂ => ⟨h₁.1.2.trans h₂.1.2.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.r6, h₂.1.1.r6]
      · rw [h₁.2.1, h₂.2.1]⟩) (by taint_decide))
    (B := fun t => RPPre b sp (Proof.X25519.toFe (decodeLE bs % 2 ^ 255)) (decodeLE bs / 2 ^ 255 == 1) t ∧
      (t.gpr .r5 = 0 ↔ decodeLE bs % 2 ^ 255 < P)) fun s h =>
      WP.mono (pointDecodeLoad_ok h.1.1 h.2.1 h.2.2.1 h.2.2.2.1) fun t ⟨k, sg, y, z⟩ => by
        rw [h.2.2.2.2] at sg y z
        exact ⟨⟨h.1.of_rest k.rest (by decide), y, sg⟩, z⟩
  refine RelCT.seq h1 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · exact (recoverPoint_ct _ _).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h

end

end VG.Proof.Ed25519.PPC64LE

end

end

/-!
# `vg_ed25519_verify_equation` on PPC64LE leaks only its inputs

Two runs with the same pointers, stack pointer, input bytes and static leak
the same trace (`verify_ct`), given the windows' constant time (`RhsCT`). As for a decoding (`DecodeCT.lean`), the taint analysis
checks the code between the branches, and each branch on a value loaded from
memory (`S < L`, both points decoded, the comparison) is related by
correctness: both runs take it on the same fact about the inputs.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P Fe)
open VG.Spec.Ed25519 (decodeLE bytesAt)

section
variable {b sp : Addr}

/-- Before the comparison: the points `p` and `q` in slots 0–3 and 4–7. -/
def EqPre (b sp : Addr) (p q : Spec.Ed25519.Point) (s : State) : Prop :=
  Pin b sp s ∧ point (env s.mem b) 0 1 2 3 = p ∧ point (env s.mem b) 4 5 6 7 = q

theorem pointEqual_ct (p q : Spec.Ed25519.Point) :
    RelCT isa (Both (EqPre b sp p q)) Impl.Ed25519.PPC64LE.pointEqual fun _ _ => True := by
  unfold Impl.Ed25519.PPC64LE.pointEqual
  let E (t : State) : Prop := Pin b sp t ∧ env t.mem b 8 = p.X * q.Z ∧ env t.mem b 9 = q.X * p.Z ∧
    env t.mem b 10 = p.Y * q.Z ∧ env t.mem b 11 = q.Y * p.Z
  have h1 := ctBoth (ctRegs [.r6] (A := EqPre b sp p q) (c := fieldCode pointEqualOps)
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide)) (B := E) fun s h =>
      WP.mono (fieldCode_ok _ h.1.1.ctx) fun t ⟨k, e⟩ => by
        refine ⟨h.1.of_rest k.rest (by decide), ?_, ?_, ?_, ?_⟩ <;> rw [e, ← h.2.1, ← h.2.2] <;> rfl
  let E' (t : State) : Prop := Pin b sp t ∧ env t.mem b 10 = p.Y * q.Z ∧ env t.mem b 11 = q.Y * p.Z
  have h2 := ctBoth (ctRegs [.r6] (A := E) (c := fieldEqual 8 9) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => E' t ∧ (t.gpr .r5 = 0 ↔ p.X * q.Z = q.X * p.Z)) fun s h =>
      WP.mono (fieldEqual_ok h.1.1.ctx 8 9) fun t ⟨k, e, z⟩ =>
        ⟨⟨h.1.of_rest k.rest (by decide), by rw [e]; exact h.2.2.2.1, by rw [e]; exact h.2.2.2.2⟩,
          by rw [z, h.2.1, h.2.2.1]⟩
  have h3 := ctBoth (ctRegs [.r6] (A := E') (c := fieldEqual 10 11) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => Pin b sp t ∧ (t.gpr .r5 = 0 ↔ p.Y * q.Z = q.Y * p.Z)) fun s h =>
      WP.mono (fieldEqual_ok h.1.1.ctx 10 11) fun t ⟨k, _, z⟩ =>
        ⟨h.1.of_rest k.rest (by decide), by rw [z, h.2.1, h.2.2]⟩
  refine RelCT.seq h1 (RelCT.seq h2 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_))
  · refine RelCT.seq (h3.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
      (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
    · exact (ctRegs [.r6] (A := Pin b sp) (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)).mono
        (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h

end

/-! ## The decoding loop -/

section
variable {b sp pk sig ch : Addr} {PK RS : List Byte}

/-- After `k` decodings, from inputs whose encodings are `PK` and `RS`. -/
def DecCT (b sp pk sig ch : Addr) (PK RS : List Byte) (k : Nat) (s : State) : Prop :=
  ∃ s0, DecInv s0 b pk sig ch k s ∧ s.sp = sp ∧ bytesAt s0.mem pk 32 = PK ∧ bytesAt s0.mem sig 32 = RS

def inBytes (PK RS : List Byte) (k : Nat) : List Byte := if k = 0 then PK else RS

theorem decodeBody_ct {k : Nat} :
    RelCT isa (Both (DecCT b sp pk sig ch PK RS k)) decodeBody fun _ _ => True := by
  unfold decodeBody
  let B1 (t : State) : Prop := DecPre b sp (inPtr pk sig k) (inBytes PK RS k) t ∧
    t.gpr .r28 = BitVec.ofNat 64 (7776 + 128 * k) ∧ t.gpr .r30 = sig
  have h1 := ctBoth (ctRegs [.r6, .r27] (A := DecCT b sp pk sig ch PK RS k) (c := .block [.addi .r14 .r27 0])
    (fun _ _ ⟨_, d₁, p₁, _⟩ ⟨_, d₂, p₂, _⟩ => ⟨p₁.trans p₂.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [d₁.ctx.ctx.r6, d₂.ctx.ctx.r6]
      · rw [d₁.r27, d₂.r27]⟩) (by taint_decide)) (B := B1) fun s ⟨s0, d, hsp, hpk, hrs⟩ => by
    have h1 : offset 1 = 96 := rfl
    refine wp_addi (by decide) (by decide) fun t1 u1 => WP.block_nil ?_
    have hv1 : VCtx b pk sig ch t1 := d.ctx.of_rest (u1.rest (ws := [.r14]) (by decide)) (by decide)
    have hq : (∀ j < 8, InRegions (t1.rd ++ t1.wr) (inPtr pk sig k + BitVec.ofNat 64 (0 + 4 * j)) 4) ∧
        (⟨inPtr pk sig k, 32⟩ : Region).Disjoint ⟨b, 8192⟩ ∧ bytesAt s0.mem (inPtr pk sig k) 32 = inBytes PK RS k := by
      unfold inPtr inBytes
      by_cases h0 : k = 0
      · rw [ite_eq_left h0, ite_eq_left h0]
        exact ⟨fun j hj => in_base (List.mem_append_left _ hv1.pkR) (by omega_using [hj]) (by omega_using [hj]), hv1.pkD, hpk⟩
      · rw [ite_eq_right h0, ite_eq_right h0]
        exact ⟨fun j hj => in_base (List.mem_append_left _ hv1.sigR) (by omega_using [hj]) (by omega_using [hj]),
          hv1.sigD.sub_left (Region.sub_prefix (by decide)), hrs⟩
    obtain ⟨hr4, hdq, hbs⟩ := hq
    refine ⟨⟨⟨hv1.ctx, by rw [u1.sp, hsp]⟩, by rw [u1.gpr, BitVec.add_zero, d.r27], hr4, by
      rw [BitVec.add_zero]; exact hdq.sub_right (Offset.sub_base b (by omega)), ?_⟩,
      by rw [u1.other _ (by decide), d.r28], by rw [u1.other _ (by decide), d.ctx.r30]⟩
    rw [u1.mem, bytesAt_ws d.frame decW_sub hdq (by decide), hbs]
  let B2 (t : State) : Prop := Pin b sp t ∧ t.gpr .r28 = BitVec.ofNat 64 (7776 + 128 * k) ∧ t.gpr .r30 = sig
  have h2 := ctBoth ((pointDecode_ct (b := b) (sp := sp) (inPtr pk sig k) (inBytes PK RS k)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) (A := B1) (B := B2) fun s h =>
      WP.mono (pointDecode_ok h.1.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1) fun t ⟨k', _⟩ =>
        ⟨h.1.1.of_rest k'.rest (by decide), by rw [k'.rest.gpr _ (by decide), h.2.1],
          by rw [k'.rest.gpr _ (by decide), h.2.2]⟩
  have h3 := ctRegs [.r6, .r28, .r30] (A := B2) (c := .block decodeNext)
    (fun _ _ h₁ h₂ => ⟨h₁.1.2.trans h₂.1.2.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1.1.r6, h₂.1.1.r6]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]⟩) (by taint_decide)
  exact RelCT.seq h1 (RelCT.seq h2 h3)

theorem decodeLoop_ct :
    RelCT isa (Both (DecCT b sp pk sig ch PK RS 0)) (.loop decodeBody (.nonzero .d .r7))
      (Both (DecCT b sp pk sig ch PK RS 2)) := by
  refine (RelCT.loop (Q := Both (DecCT b sp pk sig ch PK RS 2))
    (fun n => Both fun s => 1 ≤ n ∧ n ≤ 2 ∧ DecCT b sp pk sig ch PK RS (2 - n) s) (fun n => ?_) 2).mono
      (fun _ _ h => ⟨⟨by decide, Nat.le_refl _, h.1⟩, ⟨by decide, Nat.le_refl _, h.2⟩⟩) fun _ _ h => h
  by_cases hn : 1 ≤ n ∧ n ≤ 2
  · have hb := ctBoth ((decodeBody_ct (b := b) (sp := sp) (pk := pk) (sig := sig) (ch := ch) (PK := PK) (RS := RS)
      (k := 2 - n)).mono (fun _ _ h => ⟨h.1.2.2, h.2.2.2⟩) fun _ _ h => h)
      (A := fun s => 1 ≤ n ∧ n ≤ 2 ∧ DecCT b sp pk sig ch PK RS (2 - n) s)
      (B := fun t => DecCT b sp pk sig ch PK RS (2 - n + 1) t ∧
        t.gpr .r7 = BitVec.ofNat 64 (7776 + 128 * (2 - n + 1)) - BitVec.ofNat 64 8032)
      fun s ⟨_, _, s0, d, hsp, hpk, hrs⟩ => WP.mono (decodeBody_ok (by omega_using [hn]) d) fun t ⟨dt, e7⟩ =>
        ⟨⟨s0, dt, by rw [dt.rest.sp, ← d.rest.sp, hsp], hpk, hrs⟩, e7⟩
    refine hb.mono (fun _ _ h => h) fun s₁ s₂ ⟨⟨d₁, e₁⟩, ⟨d₂, e₂⟩⟩ =>
      ⟨by rw [eval_nonzero, eval_nonzero, e₁, e₂], fun hf => ?_, fun ht => ?_⟩
    · rcases (by omega_using [hn] : n = 1 ∨ n = 2) with rfl | rfl
      · exact ⟨d₁, d₂⟩
      · rw [eval_nonzero, e₁] at hf; exact absurd hf (by decide)
    · rcases (by omega_using [hn] : n = 1 ∨ n = 2) with rfl | rfl
      · rw [eval_nonzero, e₁] at ht; exact absurd ht (by decide)
      · exact ⟨1, by decide, ⟨by decide, by decide, d₁⟩, ⟨by decide, by decide, d₂⟩⟩
  · exact RelCT.of_false fun _ _ h => hn ⟨h.1.1, h.1.2.1⟩

end

/-! ## The body -/

section
variable {b sp pk sig ch T : Addr} {PK SG CH : List Byte}

/-- The verification's inputs, `PK`, `SG` and `CH`. -/
def VCT (b sp pk sig ch : Addr) (PK SG CH : List Byte) (s : State) : Prop :=
  VCtx b pk sig ch s ∧ s.sp = sp ∧ bytesAt s.mem pk 32 = PK ∧ bytesAt s.mem sig 64 = SG ∧ bytesAt s.mem ch 64 = CH

theorem VCT.frame {s t : State} (h : VCT b sp pk sig ch PK SG CH s) {R : List Reg} (hr' : Rest R s t)
    (hw : ∀ r ∈ [Reg.r6, .r29, .r30, .r31], r ∉ R) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩) : VCT b sp pk sig ch PK SG CH t := by
  refine ⟨h.1.of_rest hr' hw, by rw [hr'.sp, h.2.1], ?_, ?_, ?_⟩
  · rw [bytesAt_ws hf hs h.1.pkD (by decide), h.2.2.1]
  · rw [bytesAt_ws hf hs h.1.sigD (by decide), h.2.2.2.1]
  · rw [bytesAt_ws hf hs h.1.chD (by decide), h.2.2.2.2]

/-- `VCT`, with the static of `-[1]B … -[15]B` at `T`. -/
def VCS (b sp pk sig ch T : Addr) (PK SG CH : List Byte) (s : State) : Prop :=
  VCT b sp pk sig ch PK SG CH s ∧ BStat b T s ∧ s.syms bSym = T

/-- After both decodings. -/
def D2 (b sp pk sig ch T : Addr) (PK SG CH : List Byte) (t : State) : Prop :=
  ∃ s0, DecInv s0 b pk sig ch 2 t ∧ VCS b sp pk sig ch T PK SG CH s0 ∧ t.syms = s0.syms

theorem D2.sp_eq {t : State} (h : D2 b sp pk sig ch T PK SG CH t) : t.sp = sp := by
  obtain ⟨s0, d, ⟨v, _⟩, _⟩ := h; rw [d.rest.sp, v.2.1]

theorem D2.pin {t : State} (h : D2 b sp pk sig ch T PK SG CH t) : Pin b sp t := by
  have hsp := h.sp_eq
  obtain ⟨_, d, _⟩ := h
  exact ⟨d.ctx.ctx, hsp⟩

theorem D2.r18 {t : State} (h : D2 b sp pk sig ch T PK SG CH t) :
    t.gpr .r18 = if ((Spec.Ed25519.decodePoint PK).isSome && (Spec.Ed25519.decodePoint (SG.take 32)).isSome)
      then 1 else 0 := by
  obtain ⟨s0, d, ⟨v, _⟩, _⟩ := h
  have e : decOk s0.mem pk sig 2 = ((Spec.Ed25519.decodePoint (bytesAt s0.mem pk 32)).isSome &&
      (Spec.Ed25519.decodePoint (bytesAt s0.mem sig 32)).isSome) := by
    show (true && (Spec.Ed25519.decodePoint (bytesAt s0.mem (if 0 = 0 then pk else sig) 32)).isSome &&
      (Spec.Ed25519.decodePoint (bytesAt s0.mem (if 1 = 0 then pk else sig) 32)).isSome) = _
    rw [ite_eq_left rfl, ite_eq_right (by decide), Bool.true_and]
  rw [d.r18, e, v.2.2.1, ← Proof.Ed25519.signatureBytes_take, v.2.2.2.1]

theorem decodeBoth_ct :
    RelCT isa (Both (VCS b sp pk sig ch T PK SG CH)) decodeBoth (Both (D2 b sp pk sig ch T PK SG CH)) := by
  have h := RelCT.seq (ctBoth (ctRegs [.r6, .r29] (A := VCT b sp pk sig ch PK SG CH) (c := .block decodeStart)
    (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.ctx.r6, h₂.1.ctx.r6]
      · rw [h₁.1.r29, h₂.1.r29]⟩) (by taint_decide))
    (B := DecCT b sp pk sig ch PK (SG.take 32) 0) fun s h => WP.mono (decodeStart_ok h.1) fun t d =>
      ⟨s, d, by rw [d.rest.sp, h.2.1], h.2.2.1, by rw [← Proof.Ed25519.signatureBytes_take, h.2.2.2.1]⟩)
    (decodeLoop_ct (b := b) (sp := sp) (pk := pk) (sig := sig) (ch := ch) (PK := PK) (RS := SG.take 32))
  refine ctBoth ((h.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ _ => trivial)) fun s hs => ?_
  unfold decodeBoth at *
  exact WP.mono_syms (decodeBoth_ok hs.1.1) fun t d sy => ⟨s, d, hs, sy⟩

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Ed25519.bytesAt, hi]

end

/-- `verifyRhs`'s precondition: the inputs, the static at `T`, the decoded `a` and `r` in the
tables at 7776 and 7904, and the bytes `CH` of the challenge and `SS` of `S`. -/
def RhsPre (b sp pk sig ch T : Addr) (a r : Spec.Ed25519.Point) (CH SS : List Byte) (t : State) : Prop :=
  VCtx b pk sig ch t ∧ t.sp = sp ∧ BStat b T t ∧ t.syms bSym = T ∧ tableAt t.mem b 7776 = a ∧
    tableAt t.mem b 7904 = r ∧ bytesAt t.mem ch 64 = CH ∧ bytesAt t.mem (sig + BitVec.ofNat 64 32) 32 = SS

/-- **`verifyRhs` leaks only its inputs**, for decoded `a` and `r`: what the windows' proof gives
(`Proof/Ed25519/PPC64LE/Whole/VerifyMsgVerified.lean`, `rhs_ct`). -/
def RhsCT : Prop := ∀ {b sp pk sig ch T : Addr} {PK RS CH SS : List Byte} {a r : Spec.Ed25519.Point},
  Spec.Ed25519.decodePoint PK = some a → Spec.Ed25519.decodePoint RS = some r →
  RelCT isa (Both (RhsPre b sp pk sig ch T a r CH SS)) verifyRhs fun _ _ => True

section
variable {b sp pk sig ch T : Addr} {PK SG CH : List Byte}

theorem D2.rhs {t : State} {a r : Spec.Ed25519.Point} (h : D2 b sp pk sig ch T PK SG CH t)
    (ha : Spec.Ed25519.decodePoint PK = some a) (hr : Spec.Ed25519.decodePoint (SG.take 32) = some r) :
    RhsPre b sp pk sig ch T a r CH (SG.drop 32) t := by
  have hsp := h.sp_eq
  obtain ⟨s0, d, ⟨v, hB, hT⟩, sy⟩ := h
  refine ⟨d.ctx, hsp, hB.of_frame d.rest.rd d.frame decW_sub, by rw [sy, hT], ?_, ?_, ?_, ?_⟩
  · exact d.tables 0 (by decide) a (by rw [show inPtr pk sig 0 = pk from rfl, v.2.2.1]; exact ha)
  · exact d.tables 1 (by decide) r (by
      rw [show inPtr pk sig 1 = sig from rfl, ← Proof.Ed25519.signatureBytes_take, v.2.2.2.1]; exact hr)
  · rw [bytesAt_ws d.frame decW_sub d.ctx.chD (by decide), v.2.2.2.2]
  · rw [bytesAt_ws d.frame decW_sub (d.ctx.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide)))
      (by decide), ← Proof.Ed25519.signatureBytes_drop, v.2.2.2.1]

/-- The equation, for the decoded points `a` and `r`. -/
theorem verifyEquationPoints_ct (hRC : RhsCT) {a r : Spec.Ed25519.Point}
    (ha : Spec.Ed25519.decodePoint PK = some a) (hr : Spec.Ed25519.decodePoint (SG.take 32) = some r) :
    RelCT isa (Both (D2 b sp pk sig ch T PK SG CH)) verifyEquationPoints fun _ _ => True := by
  unfold verifyEquationPoints
  exact (hRC (CH := CH) (SS := SG.drop 32) ha hr).mono (fun _ _ h => ⟨h.1.rhs ha hr, h.2.rhs ha hr⟩)
    fun _ _ h => h

theorem verifyDecode_ct (hRC : RhsCT) :
    RelCT isa (Both (VCS b sp pk sig ch T PK SG CH)) verifyDecode fun _ _ => True := by
  unfold verifyDecode
  refine RelCT.seq decodeBoth_ct (RelCT.ite (fun _ _ h => by rw [eval_nonzero, eval_nonzero, h.1.r18, h.2.r18]) ?_ ?_)
  · cases ha : Spec.Ed25519.decodePoint PK with
    | some a =>
      cases hr : Spec.Ed25519.decodePoint (SG.take 32) with
      | some r => exact (verifyEquationPoints_ct hRC ha hr).mono (fun _ _ h => h.1) fun _ _ h => h
      | none =>
        refine RelCT.of_false fun _ _ h => ?_
        have e := h.1.1.r18
        rw [ha, hr] at e
        have := h.2
        rw [eval_nonzero, e] at this
        simp at this
    | none =>
      refine RelCT.of_false fun _ _ h => ?_
      have e := h.1.1.r18
      rw [ha] at e
      have := h.2
      rw [eval_nonzero, e] at this
      simp at this
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.pin, h.1.2.pin⟩) fun _ _ h => h

theorem verifyBody_ct (hRC : RhsCT) :
    RelCT isa (Both (VCS b sp pk sig ch T PK SG CH)) verifyBody fun _ _ => True := by
  unfold verifyBody
  have hFA : ∀ r ∈ [FA b], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_using [])
  have h1 := ctBoth (ctRegs [.r6, .r30] (A := VCS b sp pk sig ch T PK SG CH) (c := .block verifyScalar)
    (fun _ _ h₁ h₂ => ⟨h₁.1.2.1.trans h₂.1.2.1.symm, fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [h₁.1.1.ctx.r6, h₂.1.1.ctx.r6]
      · rw [h₁.1.1.r30, h₂.1.1.r30]⟩) (by taint_decide))
    (B := fun t => VCS b sp pk sig ch T PK SG CH t ∧
      (t.gpr .r8 = 0 ↔ decodeLE (SG.drop 32) < Spec.Ed25519.L))
    fun s h => WP.mono_syms (verifyScalar_ok h.1.1) fun t ⟨rt, ft, et⟩ sy =>
      ⟨⟨h.1.frame rt (by decide) ft hFA, h.2.1.of_frame rt.rd ft hFA, by rw [sy]; exact h.2.2⟩,
        by rw [et, ← Proof.Ed25519.signatureBytes_drop, h.1.2.2.2.1]⟩
  refine RelCT.seq h1 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · have h2 := ctBoth (ctRegs [.r6] (A := VCS b sp pk sig ch T PK SG CH) (c := .block initFields)
      (fun _ _ h₁ h₂ => ⟨h₁.1.2.1.trans h₂.1.2.1.symm, fun x hx => by
        rw [List.mem_singleton.mp hx, h₁.1.1.ctx.r6, h₂.1.1.ctx.r6]⟩) (by taint_decide))
      (B := VCS b sp pk sig ch T PK SG CH) fun s h => WP.mono_syms (initFields_ok h.1.1.ctx.ctx)
        fun t ⟨rt, ft⟩ sy => ⟨h.1.frame rt (by decide) ft hFA, h.2.1.of_frame rt.rd ft hFA, by rw [sy]; exact h.2.2⟩
    exact RelCT.seq (h2.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h) (verifyDecode_ct hRC)
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨⟨h.1.1.1.1.1.ctx, h.1.1.1.1.2.1⟩, ⟨h.1.2.1.1.1.ctx, h.1.2.1.1.2.1⟩⟩)
      fun _ _ h => h

/-- The function's precondition, with its public values. -/
def VTop (b sp pk sig ch T : Addr) (PK SG CH : List Byte) (s : State) : Prop :=
  VerifyPre s ∧ s.syms bSym = T ∧ s.gpr .r3 = pk ∧ s.gpr .r4 = sig ∧ s.gpr .r5 = ch ∧ s.gpr .r6 = b ∧ s.sp = sp ∧
    bytesAt s.mem pk 32 = PK ∧ bytesAt s.mem sig 64 = SG ∧ bytesAt s.mem ch 64 = CH

theorem verifyEquation_rel (hR : RhsOk) (hRC : RhsCT) :
    RelCT isa (Both (VTop b sp pk sig ch T PK SG CH)) Impl.Ed25519.PPC64LE.verifyEquation fun _ _ => True := by
  unfold Impl.Ed25519.PPC64LE.verifyEquation
  have h1 := ctBoth (ctRegs [.r3, .r4, .r5, .r6] (A := VTop b sp pk sig ch T PK SG CH) (c := .block verifySetup)
    (fun _ _ h₁ h₂ => ⟨h₁.2.2.2.2.2.2.1.trans h₂.2.2.2.2.2.2.1.symm, fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2.1, h₂.2.2.2.1]
      · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
      · rw [h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1]⟩) (by taint_decide))
    (B := VCS b sp pk sig ch T PK SG CH) fun s h => by
      obtain ⟨hp, hT, e3, e4, e5, e6, hsp, hpk, hsg, hch⟩ := h
      refine WP.mono_syms (verifySetup_ok hp) fun t ⟨vt, rt, _, ft, _⟩ sy => ?_
      have hB := hp.bs
      rw [e6, hT] at hB
      rw [e3, e4, e5, e6] at vt
      rw [e6] at ft
      have hs : ∀ r ∈ [(⟨b, 8192⟩ : Region)], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
        rw [List.mem_singleton.mp hr]; exact fun _ h => h
      refine ⟨⟨vt, by rw [rt.sp, hsp], ?_, ?_, ?_⟩, hB.of_frame rt.rd ft hs, by rw [sy, hT]⟩
      · rw [bytesAt_ws ft hs vt.pkD (by decide), hpk]
      · rw [bytesAt_ws ft hs vt.sigD (by decide), hsg]
      · rw [bytesAt_ws ft hs vt.chD (by decide), hch]
  have h2 := ctBoth (verifyBody_ct (b := b) (sp := sp) (pk := pk) (sig := sig) (ch := ch) (T := T) (PK := PK)
    (SG := SG) (CH := CH) hRC) (B := Pin b sp) fun s h =>
      WP.mono (verifyBody_ok hR h.1.1 (by rw [h.2.2]; exact h.2.1)) fun t ⟨rt, _, _⟩ =>
        Pin.of_rest ⟨h.1.1.ctx, h.1.2.1⟩ rt (by decide)
  exact RelCT.seq h1 (RelCT.seq h2 (ctRegs [.r6] (A := Pin b sp) (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)))

end

end VG.Proof.Ed25519.PPC64LE
