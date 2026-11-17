module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Packed
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointScalar
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarReduce
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.X25519.PPC64LE.Field
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Decode
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target

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
