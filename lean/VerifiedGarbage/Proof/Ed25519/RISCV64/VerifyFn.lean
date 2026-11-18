module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarReduce
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed25519.RISCV64.Decode
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.TCB.RISCV64.Target

/-! ### `Ed25519.RISCV64.VerifyBody`, which only this module used -/

section

/-!
# Ed25519 on RISC-V: the body of the verification

`S < L` (`verifyScalar_ok`), then `A` and `R` decoded by one loop of two
iterations into the tables at 7776 and 7904 (`decodeBoth_ok`, its invariant
`DecInv`), then the equation if both are points (`verifyDecode_ok`): in `s3`,
`verifyEquation` of the inputs (`verifyBody_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
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
  obtain l32 : (bytesAt m pk 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  obtain l64 : (bytesAt m sig 64).length = 64 := by simp [Spec.Ed25519.bytesAt]
  obtain l64' : (bytesAt m ch 64).length = 64 := by simp [Spec.Ed25519.bytesAt]
  unfold Spec.Ed25519.verifyEquation eqResult
  rw [l32, l64, l64', Proof.Ed25519.signatureBytes_take, Proof.Ed25519.signatureBytes_drop]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  cases Spec.Ed25519.decodePoint (bytesAt m pk 32) <;> cases Spec.Ed25519.decodePoint (bytesAt m sig 32) <;> simp

section
variable {b pk sig ch : Addr}

/-- **`S < L`**: `a5` zero exactly when the signature's second half is below `L`. -/
theorem verifyScalar_ok {s : State} (h : VCtx b pk sig ch s) :
    WP isa (.block verifyScalar) s fun t =>
      Rest [.a2, .a4, .a5, .s0] s t ∧ Frame [FA b] s.mem t.mem ∧
      (t.gpr .a5 = 0 ↔ decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 32) 32) < Spec.Ed25519.L) := by
  have hS := SR_eq
  have hD := SD_eq
  rw [show verifyScalar = .addi .s0 .s10 32 ::
    (unpackField .s0 SR 0 ++ (.li .a5 1 :: VG.Impl.X25519.RISCV64.pass .a3 SD scalarSubtractSrc)) from rfl]
  refine wp_addi (by decide) fun s1 u1 => ?_
  obtain hc1 : Ctx8 b s1 := h.ctx.of_rest (u1.rest (ws := [.s0]) (by decide)) (by decide)
  refine WP.append (unpackField_ok hc1.ctx (q := sig + BitVec.ofNat 64 32) (o := SR) (src := 0) (by decide)
    (by rw [u1.gpr, h.s10]) (by decide) (by decide) (by decide)
    (fun k hk => by
      rw [u1.rd, u1.wr, Offset.add_add]
      exact in_base (List.mem_append_left _ h.sigR) (by omega_arith) (by omega_arith))
    (by
      rw [BitVec.add_zero]
      exact (h.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide))).sub_right
        (Offset.sub_base b (by omega_arith))))
    fun s2 ⟨r2, f2, l2⟩ => ?_
  obtain hv : decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 32) 32) = V s2.mem b SR :=
    bytes_of_words fun j hj => by rw [l2 j hj, Nat.zero_add, ← u1.mem]
  refine wp_li (by decide) fun s3 u3 => ?_
  obtain hc3 : Ctx b s3 := hc1.ctx.of_rest ((r2.mono (ws' := [.a4, .a5]) (by decide)).trans (u3.rest (by decide)))
    (by decide)
  refine WP.mono (subtract_ok hc3 u3.gpr) fun t ⟨r4, f4, l4, e8, _⟩ => ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((u3.rest (by decide)).trans (r4.mono (by decide))))
  · rw [← u1.mem]
    obtain fa : Frame [FA b] s1.mem s2.mem := f2.sub fun r hr => ⟨FA b, by simp, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_arith) (by omega_arith)⟩
    obtain fb : Frame [FA b] s2.mem t.mem := by
      rw [← u3.mem]
      exact f4.sub fun r hr => ⟨FA b, by simp, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_arith) (by omega_arith)⟩
    exact fa.trans fb
  · have hz : t.gpr .a5 = 0 ↔ (t.gpr .a5).toNat = 0 :=
      ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
    obtain hv3 : V s3.mem b SR = V s2.mem b SR := by rw [u3.mem]
    rw [hz, e8, hv, ← hv3]
    by_cases hL : Spec.Ed25519.L ≤ V s3.mem b SR
    · rw [iteT hL]; exact ⟨fun h => absurd h (by decide), fun h => absurd hL (by omega_arith)⟩
    · rw [iteF hL]; exact ⟨fun _ => by omega_arith, fun _ => rfl⟩

/-! ## Decoding `A` and `R` -/

def inPtr (pk sig : Addr) (k : Nat) : Addr := if k = 0 then pk else sig

/-- Whether the first `k` inputs decode to points. -/
def decOk (m : Mem) (pk sig : Addr) : Nat → Bool
  | 0 => true
  | k + 1 => decOk m pk sig k && (Spec.Ed25519.decodePoint (bytesAt m (inPtr pk sig k) 32)).isSome

/-- What the decoding loop writes. -/
abbrev decW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 SIGN, 4⟩, FA b, ⟨b + BitVec.ofNat 64 7776, 256⟩]

abbrev decR : List Reg := .a4 :: .s0 :: .s4 :: .s7 :: .s8 :: .s3 :: fclob

/-- After `k` decodings from `s0`. -/
structure DecInv (s0 : State) (b pk sig ch : Addr) (k : Nat) (t : State) : Prop where
  ctx : VCtx b pk sig ch t
  rest : Rest decR s0 t
  frame : Frame (decW b) s0.mem t.mem
  s7 : t.gpr .s7 = inPtr pk sig k
  s8 : t.gpr .s8 = BitVec.ofNat 64 (7776 + 128 * k)
  s4 : t.gpr .s4 = if decOk s0.mem pk sig k then 1 else 0
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

/-- The decoding's result recorded: `s4`, the table entry, the next input. -/
theorem decodeNext_ok {s0 t u : State} {k : Nat} (hk : k < 2) (h : DecInv s0 b pk sig ch k t) {q : Addr}
    (hq : q = inPtr pk sig k) (hRt : Rest (.s0 :: .s3 :: fclob) t u)
    (hfu : Frame [⟨b + BitVec.ofNat 64 SIGN, 4⟩, FA b] t.mem u.mem) (hvu : VCtx b pk sig ch u)
    {o : Option Spec.Ed25519.Point} (ho : Spec.Ed25519.decodePoint (bytesAt s0.mem q 32) = o)
    (du : DecodeResult b o u) :
    WP isa (.block decodeNext) u fun w => DecInv s0 b pk sig ch (k + 1) w ∧
      w.gpr .a4 = BitVec.ofNat 64 (7776 + 128 * (k + 1)) - BitVec.ofNat 64 8032 := by
  have hS : SIGN = 24 := rfl
  unfold decodeNext
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_and fun u1' v1 => wp_add fun u2' v2 => ?_
  obtain hR2 : Rest [.s4, .s0] u u2' := (v1.rest (by decide)).trans (v2.rest (by decide))
  obtain e14' : u2'.gpr .s0 = b + BitVec.ofNat 64 (7776 + 128 * k) := by
    rw [v2.gpr, v1.other _ (by decide), hvu.ctx.a3, v1.other _ (by decide), hRt.gpr _ (by decide), h.s8]
  obtain hv2 : VCtx b pk sig ch u2' := hvu.of_rest hR2 (by decide)
  obtain ho1 : 1024 ≤ 7776 + 128 * k := by omega_using []
  obtain ho2 : 7776 + 128 * k + 128 ≤ 8192 := by omega_using [hk]
  obtain hpt := pointToTable_ok hv2.ctx e14' ho1 ho2
  refine WP.block_append_iff.mpr (WP.mono hpt fun w ⟨rw', fw, tw⟩ => ?_)
  refine wp_mv fun w1 x1 => wp_addi (by decide) fun w2 x2 => ?_
  refine WP.append (ByteLoad.li32_ok (d := .a4) _) fun w25 e25 => ?_
  obtain x25 : Upd w2 w25 .a4 (BitVec.ofNat 64 8032) := by rw [e25, sext_ofNat (by decide)]; exact Upd.write _ _ _
  refine wp_sub fun w3 x3 => WP.block_nil ⟨?_, ?_⟩
  · have hRw : Rest decR u w3 := (hR2.mono (by decide)).trans ((rw'.mono (by decide)).trans
      ((x1.rest (by decide)).trans ((x2.rest (by decide)).trans ((x25.rest (by decide)).trans
        (x3.rest (by decide))))))
    obtain hm3 : w3.mem = w.mem := by rw [x3.mem, x25.mem, x2.mem, x1.mem]
    obtain hmu : u2'.mem = u.mem := by rw [v2.mem, v1.mem]
    obtain e28 : w1.gpr .s8 = BitVec.ofNat 64 (7776 + 128 * k) := by
      rw [x1.other _ (by decide), rw'.gpr _ (by decide), hR2.gpr _ (by decide), hRt.gpr _ (by decide), h.s8]
    refine ⟨hvu.of_rest hRw (by decide), h.rest.trans ((hRt.mono (by decide)).trans hRw), ?_, ?_, ?_, ?_,
      fun j hj p hp => ?_⟩
    · have f1 : Frame (decW b) t.mem u.mem := hfu.mono (by simp)
      obtain f2 : Frame (decW b) u.mem w3.mem := by
        rw [hm3, ← hmu]
        exact fw.sub fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact ⟨⟨b + BitVec.ofNat 64 7776, 256⟩, by simp, Offset.sub b (by omega_arith) (by omega_arith)⟩
      exact h.frame.trans (f1.trans f2)
    · rw [x3.other _ (by decide), x25.other _ (by decide), x2.other _ (by decide), x1.gpr, rw'.gpr _ (by decide),
        hR2.gpr _ (by decide), hvu.s10]
      unfold inPtr; rw [iteF (by omega_arith)]
    · rw [x3.other _ (by decide), x25.other _ (by decide), x2.gpr, e28, BitVec.ofNat_add_ofNat]
      congr 1
    · rw [x3.other _ (by decide), x25.other _ (by decide), x2.other _ (by decide), x1.other _ (by decide),
        rw'.gpr _ (by decide), v2.other _ (by decide), v1.gpr, hRt.gpr _ (by decide), h.s4]
      obtain e17 : u.gpr .s3 = if o.isSome then 1 else 0 := by
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
  · rw [x3.gpr, x25.gpr, x25.other _ (by decide), x2.gpr, x1.other _ (by decide), rw'.gpr _ (by decide),
      hR2.gpr _ (by decide),
      hRt.gpr _ (by decide), h.s8, BitVec.ofNat_add_ofNat]
    congr 2

/-- **One decoding**, of input `k`. -/
theorem decodeBody_ok {s0 t : State} {k : Nat} (hk : k < 2) (h : DecInv s0 b pk sig ch k t) :
    WP isa decodeBody t fun u => DecInv s0 b pk sig ch (k + 1) u ∧
      u.gpr .a4 = BitVec.ofNat 64 (7776 + 128 * (k + 1)) - BitVec.ofNat 64 8032 := by
  have hS : SIGN = 24 := rfl
  have h1 : offset 1 = 96 := rfl
  unfold decodeBody
  refine WP.seq (wp_mv fun t1 u1 => WP.block_nil ?_)
  obtain hv1 : VCtx b pk sig ch t1 := h.ctx.of_rest (u1.rest (ws := [.s0]) (by decide)) (by decide)
  obtain ⟨q, hq⟩ : ∃ q, q = inPtr pk sig k := ⟨_, rfl⟩
  obtain e14 : t1.gpr .s0 = q := by rw [u1.gpr, h.s7, hq]
  obtain hqR : (∀ j < 8, InRegions (t1.rd ++ t1.wr) (q + BitVec.ofNat 64 (0 + 4 * j)) 4) ∧
      (⟨q, 32⟩ : Region).Disjoint ⟨b, 8192⟩ := by
    rw [hq]; unfold inPtr
    by_cases h0 : k = 0
    · rw [iteT h0]
      exact ⟨fun j hj => in_base (List.mem_append_left _ hv1.pkR) (by omega_arith) (by omega_arith), hv1.pkD⟩
    · rw [iteF h0]
      exact ⟨fun j hj => in_base (List.mem_append_left _ hv1.sigR) (by omega_arith) (by omega_arith),
        hv1.sigD.sub_left (Region.sub_prefix (by decide))⟩
  obtain ⟨hr4, hdq⟩ := hqR
  obtain hb : bytesAt t1.mem q 32 = bytesAt s0.mem q 32 := by
    rw [u1.mem]; exact bytesAt_ws h.frame decW_sub hdq (by decide)
  refine WP.seq (WP.mono (pointDecode_ok hv1.ctx e14 hr4 (by
    rw [BitVec.add_zero]; exact hdq.sub_right (Offset.sub_base b (by omega_arith)))) fun u ⟨ku, o, ho, du⟩ =>
      decodeNext_ok hk h hq ((u1.rest (by decide)).trans (ku.rest.mono (by decide)))
        (by rw [← u1.mem]; exact ku.frame) (hv1.of_rest ku.rest (by decide)) (by rw [← hb]; exact ho) du)

theorem decodeStart_ok {s : State} (h : VCtx b pk sig ch s) :
    WP isa (.block decodeStart) s (DecInv s b pk sig ch 0) := by
  unfold decodeStart
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s1 u1 => WP.append (ByteLoad.li32_ok (d := .s8) _) fun s2 e2 => ?_
  obtain u2 : Upd s1 s2 .s8 (BitVec.ofNat 64 7776) := by rw [e2, sext_ofNat (by decide)]; exact Upd.write _ _ _
  refine wp_li (by decide) fun s3 u3 => WP.block_nil ?_
  obtain hr3 : Rest [.s7, .s8, .s4] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  exact ⟨h.of_rest hr3 (by decide), hr3.mono (by decide), by rw [u3.mem, u2.mem, u1.mem]; exact Frame.refl _ _,
    by rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, h.s9]; rfl,
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
  ⟨b + BitVec.ofNat 64 SIGN, 4⟩ :: ⟨b + BitVec.ofNat 64 7776, 256⟩ :: sideW b 8032

abbrev verR : List Reg := .s4 :: .s7 :: .s8 :: .s3 :: sideR

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
      t.gpr .s3 = if eqResult s.mem pk sig ch then 1 else 0 := by
  unfold verifyDecode
  refine WP.seq (WP.mono_syms (decodeBoth_ok h) fun s1 h1 sy1 => ?_)
  obtain hf1 : Frame (verW b) s.mem s1.mem := h1.frame.mono (by simp)
  obtain he1 : eqResult s1.mem pk sig ch = eqResult s.mem pk sig ch := eqResult_frame h1.frame decW_sub h
  obtain hB1 : BStat b (s1.syms bSym) s1 := by
    rw [sy1]; exact hB.of_frame h1.rest.rd h1.frame decW_sub
  refine WP.ite (s1.gpr .s4 != 0) (eval_nonzero s1 .s4) (fun hb => ?_) (fun hb => ?_)
  · have hok : decOk s.mem pk sig 2 = true := by
      rw [h1.s4] at hb
      revert hb; cases decOk s.mem pk sig 2 <;> decide
    simp only [decOk, Bool.true_and, Bool.and_eq_true] at hok
    obtain ⟨ha, hr⟩ := hok
    obtain ⟨a, ea⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨r, er⟩ := Option.isSome_iff_exists.mp hr
    obtain ta : tableAt s1.mem b 7776 = a := h1.tables 0 (by decide) a ea
    obtain tr : tableAt s1.mem b 7904 = r := h1.tables 1 (by decide) r er
    unfold verifyEquationPoints
    refine WP.mono (hR h1.ctx hB1 (by rw [ta]; exact ea) (by rw [tr]; exact er)) fun t ⟨rt, ft, et⟩ =>
      ⟨?_, ?_, ?_⟩
    · exact (h1.rest.mono (by decide)).trans (rt.mono (by decide))
    · exact hf1.trans (ft.mono (by simp))
    · rw [et, ta, tr, bytesAt_ws h1.frame decW_sub h.chD (by decide),
        bytesAt_ws h1.frame decW_sub (h.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide)))
          (by decide)]
      unfold eqResult
      simp only [inPtr, iteT] at ea er
      rw [show (if (1 : Nat) = 0 then pk else sig) = sig from rfl] at er
      rw [ea, er]
  · have hno : decOk s.mem pk sig 2 = false := by
      rw [h1.s4] at hb
      revert hb; cases decOk s.mem pk sig 2 <;> decide
    refine WP.mono (recoverInvalid_ok (b := b) s1) fun t ⟨kt, mt, dt⟩ => ⟨?_, ?_, ?_⟩
    · exact (h1.rest.mono (by decide)).trans (kt.rest.mono (by decide))
    · rw [mt]; exact hf1
    · rw [show t.gpr .s3 = 0 from dt]
      simp only [decOk, Bool.true_and, Bool.and_eq_false_iff] at hno
      obtain hf : eqResult s.mem pk sig ch = false := by
        unfold eqResult
        simp only [inPtr, ↓reduceIte, Nat.one_ne_zero] at hno
        revert hno
        cases Spec.Ed25519.decodePoint (bytesAt s.mem pk 32) <;>
          cases Spec.Ed25519.decodePoint (bytesAt s.mem sig 32) <;> simp
      rw [hf]; rfl

/-- **The verification's body**: `verifyEquation` of the inputs, in `s3`. -/
theorem verifyBody_ok (hR : RhsOk) {s : State} (h : VCtx b pk sig ch s) (hB : BStat b (s.syms bSym) s) :
    WP isa verifyBody s fun t => Rest verR s t ∧ Frame (verW b) s.mem t.mem ∧
      t.gpr .s3 = if Spec.Ed25519.verifyEquation (bytesAt s.mem pk 32) (bytesAt s.mem sig 64)
        (bytesAt s.mem ch 64) then 1 else 0 := by
  unfold verifyBody
  refine WP.seq (WP.mono_syms (verifyScalar_ok h) fun s1 ⟨r1, f1, h8⟩ sy1 => ?_)
  rw [verifyEquation_eq]
  obtain hv1 : VCtx b pk sig ch s1 := h.of_rest r1 (by decide)
  obtain hF : ∀ r ∈ [FA b], r ∈ verW b := by simp
  refine WP.ite (s1.gpr .a5 == 0) (eval_zero s1 .a5) (fun hz => ?_) (fun hz => ?_)
  · have hlt := h8.mp (beq_iff_eq.mp hz)
    refine WP.seq (WP.mono_syms (initFields_ok hv1.ctx.ctx) fun s2 ⟨r2, f2⟩ sy2 => ?_)
    obtain hB2 : BStat b (s2.syms bSym) s2 := by
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
    · rw [show t.gpr .s3 = 0 from dt, decide_eq_false hge, Bool.false_and]; rfl

end

end VG.Proof.Ed25519.RISCV64

end

end


/-!
# `vg_ed25519_verify_equation` on RISC-V

The callee-saved registers and `ra` saved at `SAVE` of `scratch` (`a3`),
which is aligned to 8 bytes, the pointers moved to `s9`–`s11`, the body
(`verifyBody_ok`), and its result returned in `a0` (`verify_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (decodeLE bytesAt)

/-- The precondition, by register: `pk` in `a0`, the signature in `a1`, the challenge in `a2` and
`scratch`, aligned, in `a3`; the static of `-[1]B … -[15]B` at `bSym`. -/
structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a1, 64⟩, ⟨s.gpr .a2, 64⟩, ⟨s.syms bSym, 1920⟩]
  wr : s.wr = [⟨s.gpr .a3, 8192⟩]
  al : (s.gpr .a3).toNat % 8 = 0
  pk_ws : (⟨s.gpr .a0, 32⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  sig_ws : (⟨s.gpr .a1, 64⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  ch_ws : (⟨s.gpr .a2, 64⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  /-- The static of `-[1]B … -[15]B`. -/
  bs : BStat (s.gpr .a3) (s.syms bSym) s

/-- The saved registers' slots. -/
def saveList : List (Reg × Nat) := (List.range 13).map fun i => (savedRegs.getD i .s0, SAVE + 8 * i)

theorem regsSave_eq : regsSave = Spill.saveCode .a3 saveList := by
  simp only [regsSave, Spill.saveCode, saveList, List.map_map]; rfl

theorem regsRestore_eq : regsRestore = Spill.restoreCode .a3 saveList := by
  simp only [regsRestore, Spill.restoreCode, saveList, List.map_map]; rfl

theorem saveList_in : ∀ p ∈ saveList, 1024 ≤ p.2 ∧ p.2 + 8 ≤ 1024 + 104 := by decide

theorem saveList_fits : ∀ p ∈ saveList, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem saveList_restorable : Spill.Restorable .a3 saveList := by decide

theorem saveList_regs : saveList.map Prod.fst = savedRegs := by decide

theorem mulW_saves {B : Addr} (lo n : Nat) (h1 : 1024 ≤ lo) (h2 : lo + n ≤ 1632) :
    ∀ r ∈ pmulW B, Region.Disjoint ⟨B + BitVec.ofNat 64 lo, n⟩ r := by
  intro r hr
  have hB : BITSB = 32 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega_using [h2])) (by omega_using [h2]) (by omega_using [])
  · exact Offset.disjoint _ (.inr (by omega_using [h1])) (by omega_using [h2]) (by omega_using [])
  · exact Offset.disjoint _ (.inl (by omega_using [h2])) (by omega_using [h2]) (by omega_using [])
  · exact Offset.disjoint _ (.inr (by omega_using [h1, hB])) (by omega_using [h2]) (by omega_using [hB])

/-- The regions the verification writes are clear of the saved registers'. -/
theorem verW_saves {B : Addr} (lo n : Nat) (h1 : 1024 ≤ lo) (h2 : lo + n ≤ 1632) :
    ∀ r ∈ verW B, Region.Disjoint ⟨B + BitVec.ofNat 64 lo, n⟩ r := by
  intro r hr
  have hS : SIGN = 24 := rfl
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.disjoint _ (.inr (by omega_using [h1, hS])) (by omega_using [h2]) (by omega_using [hS])
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.disjoint _ (.inl (by omega_using [h2])) (by omega_using [h2]) (by omega_using [])
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.disjoint _ (.inl (by omega_using [h2])) (by omega_using [h2]) (by omega_using [])
  exact mulW_saves lo n h1 h2 r hr

/-- **The setup**: the registers saved, the pointers in `s9`–`s11`. -/
theorem verifySetup_ok {s : State} (hp : VerifyPre s) :
    WP isa (.block verifySetup) s fun t =>
      VCtx (s.gpr .a3) (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) t ∧ Rest [.s9, .s10, .s11] s t ∧
      Frame [⟨s.gpr .a3, 8192⟩] s.mem t.mem ∧ Spill.Saved (s.gpr .a3) s.gpr saveList t.mem := by
  have hV : SAVE = 1024 := rfl
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .a3 := ⟨_, rfl⟩
  obtain hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  unfold verifySetup
  rw [regsSave_eq]
  obtain hsin : ∀ p ∈ saveList, InRegions s.wr (s.gpr .a3 + BitVec.ofNat 64 p.2) 8 := fun p hpl => by
    have := saveList_in p hpl
    rw [← hb]; exact in_base hws (by omega_using [this]) (by omega_using [this])
  refine Spill.save_ok (b := .a3) hp.al saveList_fits hsin ?_
  generalize hs1 : ({ s with mem := Spill.saveMem s.mem (s.gpr .a3) s.gpr saveList } : State) = s1
  obtain hsv : Spill.Saved b s.gpr saveList s1.mem := by
    rw [← hs1, hb]; exact Spill.saveMem_saved (by decide) _ _ _
  obtain hf1 : Frame [⟨b, 8192⟩] s.mem s1.mem := by
    rw [← hs1, hb]
    exact Spill.saveMem_frame_base (fun p hpl => by have := saveList_in p hpl; omega_using [this]) (by decide) _ _ _
  obtain hg1 : s1.gpr = s.gpr := by rw [← hs1]
  obtain hrd1 : s1.rd = s.rd := by rw [← hs1]
  obtain hwr1 : s1.wr = s.wr := by rw [← hs1]
  obtain hsp1 : s1.sp = s.sp := by rw [← hs1]
  refine wp_mv fun s2 u2 => wp_mv fun s3 u3 => wp_mv fun s4 u4 => WP.block_nil ?_
  obtain hr4 : Rest [.s9, .s10, .s11] s1 s4 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  obtain hR4 : Rest [.s9, .s10, .s11] s s4 :=
    ⟨fun r hr => by rw [hr4.gpr _ hr, hg1], by rw [hr4.rd, hrd1], by rw [hr4.wr, hwr1], by rw [hr4.sp, hsp1]⟩
  obtain hm4 : s4.mem = s1.mem := by rw [u4.mem, u3.mem, u2.mem]
  obtain hv4 : VCtx b (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) s4 := {
    ctx := ⟨by rw [hR4.gpr _ (by decide), hb], by rw [hb]; exact hp.al, by rw [hR4.wr]; exact hws⟩
    s9 := by rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, hg1]
    s10 := by rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), hg1]
    s11 := by rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), hg1]
    pkR := by rw [hR4.rd, hp.rd]; simp
    sigR := by rw [hR4.rd, hp.rd]; simp
    chR := by rw [hR4.rd, hp.rd]; simp
    pkD := hb ▸ hp.pk_ws
    sigD := hb ▸ hp.sig_ws
    chD := hb ▸ hp.ch_ws }
  exact ⟨hb ▸ hv4, hR4, hb ▸ (by rw [hm4]; exact hf1), hb ▸ (by rw [hm4]; exact hsv)⟩

theorem verify_ok (hR : RhsOk) {s : State} (hp : VerifyPre s) :
    WP isa Impl.Ed25519.RISCV64.verifyEquation s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.gpr .ra = s.gpr .ra ∧
      t.gpr .a0 = if Spec.Ed25519.verifyEquation (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 64)
        (bytesAt s.mem (s.gpr .a2) 64) then 1 else 0 := by
  have hV : SAVE = 1024 := rfl
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .a3 := ⟨_, rfl⟩
  obtain hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  unfold Impl.Ed25519.RISCV64.verifyEquation
  refine WP.seq (WP.mono_syms (verifySetup_ok hp) fun s5 ⟨hv5, hR5, hF5, hsv⟩ sy5 => ?_)
  rw [← hb] at hv5 hF5 hsv
  obtain hsub : ∀ r ∈ [(⟨b, 8192⟩ : Region)], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact fun _ h => h
  obtain hbytes : Spec.Ed25519.verifyEquation (bytesAt s5.mem (s.gpr .a0) 32) (bytesAt s5.mem (s.gpr .a1) 64)
      (bytesAt s5.mem (s.gpr .a2) 64) = Spec.Ed25519.verifyEquation (bytesAt s.mem (s.gpr .a0) 32)
        (bytesAt s.mem (s.gpr .a1) 64) (bytesAt s.mem (s.gpr .a2) 64) := by
    rw [bytesAt_ws hF5 hsub hv5.pkD (by decide), bytesAt_ws hF5 hsub hv5.sigD (by decide),
      bytesAt_ws hF5 hsub hv5.chD (by decide)]
  obtain hB5 : BStat b (s5.syms bSym) s5 := by
    rw [sy5]
    exact (hb ▸ hp.bs).of_frame hR5.rd hF5 hsub
  refine WP.seq (WP.mono (verifyBody_ok hR hv5 hB5) fun s7 ⟨r7, f7, e17⟩ => ?_)
  rw [hbytes] at e17
  -- The result, then the registers restored.
  unfold verifyFinish
  rw [regsRestore_eq]
  obtain hc7 : Ctx8 b s7 := hv5.ctx.of_rest r7 (by decide)
  refine wp_mv fun v uv => ?_
  obtain hsv7 : Spill.Saved b s.gpr saveList v.mem := by
    rw [uv.mem]
    exact hsv.frame_in (lo := 1024) (n := 104) saveList_in f7 (verW_saves 1024 104 (by omega_using []) (by omega_using []))
  obtain e6v : v.gpr .a3 = b := by rw [uv.other _ (by decide), hc7.a3]
  rw [← List.append_nil (Spill.restoreCode .a3 saveList)]
  refine Spill.restore_ok (b := .a3) (B := b) hc7.al e6v saveList_fits saveList_restorable
    (fun p hpl => by
      have := saveList_in p hpl
      rw [uv.rd, uv.wr, r7.rd, r7.wr, hR5.rd, hR5.wr]
      exact in_base (List.mem_append_right _ hws) (by omega_using [this]) (by omega_using [this])) hsv7 fun t ht => WP.block_nil
      ⟨fun r hr => ?_, by rw [ht.sp, uv.sp, r7.sp, hR5.sp], ?_, ?_⟩
  · exact ht.gpr_of (.inl (by rw [saveList_regs]; revert hr; cases r <;> decide))
  · exact ht.gpr_of (.inl (by rw [saveList_regs]; decide))
  · rw [ht.other _ (by decide), uv.gpr, e17]

end VG.Proof.Ed25519.RISCV64
