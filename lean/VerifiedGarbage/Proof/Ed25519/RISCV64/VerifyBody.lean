module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointScalar
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarCompare
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarReduce
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed25519.RISCV64.Decode
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Field

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
  have l32 : (bytesAt m pk 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  have l64 : (bytesAt m sig 64).length = 64 := by simp [Spec.Ed25519.bytesAt]
  have l64' : (bytesAt m ch 64).length = 64 := by simp [Spec.Ed25519.bytesAt]
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
  have hc1 : Ctx8 b s1 := h.ctx.of_rest (u1.rest (ws := [.s0]) (by decide)) (by decide)
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
  have hv : decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 32) 32) = V s2.mem b SR :=
    bytes_of_words fun j hj => by rw [l2 j hj, Nat.zero_add, ← u1.mem]
  refine wp_li (by decide) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc1.ctx.of_rest ((r2.mono (ws' := [.a4, .a5]) (by decide)).trans (u3.rest (by decide)))
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
  · have hz : t.gpr .a5 = 0 ↔ (t.gpr .a5).toNat = 0 :=
      ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
    have hv3 : V s3.mem b SR = V s2.mem b SR := by rw [u3.mem]
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
  have hR2 : Rest [.s4, .s0] u u2' := (v1.rest (by decide)).trans (v2.rest (by decide))
  have e14' : u2'.gpr .s0 = b + BitVec.ofNat 64 (7776 + 128 * k) := by
    rw [v2.gpr, v1.other _ (by decide), hvu.ctx.a3, v1.other _ (by decide), hRt.gpr _ (by decide), h.s8]
  have hv2 : VCtx b pk sig ch u2' := hvu.of_rest hR2 (by decide)
  have ho1 : 1024 ≤ 7776 + 128 * k := by omega
  have ho2 : 7776 + 128 * k + 128 ≤ 8192 := by omega
  have hpt := pointToTable_ok hv2.ctx e14' ho1 ho2
  refine WP.block_append_iff.mpr (WP.mono hpt fun w ⟨rw', fw, tw⟩ => ?_)
  refine wp_mv fun w1 x1 => wp_addi (by decide) fun w2 x2 => ?_
  refine WP.append (ByteLoad.li32_ok (d := .a4) _) fun w25 e25 => ?_
  have x25 : Upd w2 w25 .a4 (BitVec.ofNat 64 8032) := by rw [e25, sext_ofNat (by decide)]; exact Upd.write _ _ _
  refine wp_sub fun w3 x3 => WP.block_nil ⟨?_, ?_⟩
  · have hRw : Rest decR u w3 := (hR2.mono (by decide)).trans ((rw'.mono (by decide)).trans
      ((x1.rest (by decide)).trans ((x2.rest (by decide)).trans ((x25.rest (by decide)).trans
        (x3.rest (by decide))))))
    have hm3 : w3.mem = w.mem := by rw [x3.mem, x25.mem, x2.mem, x1.mem]
    have hmu : u2'.mem = u.mem := by rw [v2.mem, v1.mem]
    have e28 : w1.gpr .s8 = BitVec.ofNat 64 (7776 + 128 * k) := by
      rw [x1.other _ (by decide), rw'.gpr _ (by decide), hR2.gpr _ (by decide), hRt.gpr _ (by decide), h.s8]
    refine ⟨hvu.of_rest hRw (by decide), h.rest.trans ((hRt.mono (by decide)).trans hRw), ?_, ?_, ?_, ?_,
      fun j hj p hp => ?_⟩
    · have f1 : Frame (decW b) t.mem u.mem := hfu.mono (by simp)
      have f2 : Frame (decW b) u.mem w3.mem := by
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
      have e17 : u.gpr .s3 = if o.isSome then 1 else 0 := by
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
  have hv1 : VCtx b pk sig ch t1 := h.ctx.of_rest (u1.rest (ws := [.s0]) (by decide)) (by decide)
  obtain ⟨q, hq⟩ : ∃ q, q = inPtr pk sig k := ⟨_, rfl⟩
  have e14 : t1.gpr .s0 = q := by rw [u1.gpr, h.s7, hq]
  have hqR : (∀ j < 8, InRegions (t1.rd ++ t1.wr) (q + BitVec.ofNat 64 (0 + 4 * j)) 4) ∧
      (⟨q, 32⟩ : Region).Disjoint ⟨b, 8192⟩ := by
    rw [hq]; unfold inPtr
    by_cases h0 : k = 0
    · rw [iteT h0]
      exact ⟨fun j hj => in_base (List.mem_append_left _ hv1.pkR) (by omega_arith) (by omega_arith), hv1.pkD⟩
    · rw [iteF h0]
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
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s1 u1 => WP.append (ByteLoad.li32_ok (d := .s8) _) fun s2 e2 => ?_
  have u2 : Upd s1 s2 .s8 (BitVec.ofNat 64 7776) := by rw [e2, sext_ofNat (by decide)]; exact Upd.write _ _ _
  refine wp_li (by decide) fun s3 u3 => WP.block_nil ?_
  have hr3 : Rest [.s7, .s8, .s4] s s3 :=
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

theorem verW_sub : ∀ r ∈ verW b, Region.Sub r ⟨b, 8192⟩ := by
  intro r hr
  have hS : SIGN = 24 := rfl
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.sub_base _ (by omega_arith)
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.sub_base _ (by omega_arith)
  exact sideW_sub (by decide) r hr

theorem eqResult_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩)
    {s : State} (h : VCtx b pk sig ch s) : eqResult m' pk sig ch = eqResult m pk sig ch := by
  unfold eqResult
  rw [bytesAt_ws hf hs h.pkD (by decide), bytesAt_ws hf hs (h.sigD.sub_left (Region.sub_prefix (by decide)))
      (by decide),
    bytesAt_ws hf hs (h.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide))) (by decide),
    bytesAt_ws hf hs h.chD (by decide)]

/-- **The equation, if `A` and `R` are points.** -/
theorem verifyDecode_ok {s : State} (h : VCtx b pk sig ch s) :
    WP isa verifyDecode s fun t => Rest verR s t ∧ Frame (verW b) s.mem t.mem ∧
      t.gpr .s3 = if eqResult s.mem pk sig ch then 1 else 0 := by
  unfold verifyDecode
  refine WP.seq (WP.mono (decodeBoth_ok h) fun s1 h1 => ?_)
  have hf1 : Frame (verW b) s.mem s1.mem := h1.frame.mono (by simp)
  have he1 : eqResult s1.mem pk sig ch = eqResult s.mem pk sig ch := eqResult_frame h1.frame decW_sub h
  refine WP.ite (s1.gpr .s4 != 0) (eval_nonzero s1 .s4) (fun hb => ?_) (fun hb => ?_)
  · have hok : decOk s.mem pk sig 2 = true := by
      rw [h1.s4] at hb
      revert hb; cases decOk s.mem pk sig 2 <;> decide
    simp only [decOk, Bool.true_and, Bool.and_eq_true] at hok
    obtain ⟨ha, hr⟩ := hok
    obtain ⟨a, ea⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨r, er⟩ := Option.isSome_iff_exists.mp hr
    have ta : tableAt s1.mem b 7776 = a := h1.tables 0 (by decide) a ea
    have tr : tableAt s1.mem b 7904 = r := h1.tables 1 (by decide) r er
    unfold verifyEquationPoints
    refine WP.seq (WP.mono (verifyLhs_ok h1.ctx) fun s2 ⟨r2, f2, t2⟩ => ?_)
    have h2 : VCtx b pk sig ch s2 := h1.ctx.of_rest r2 (by decide)
    refine WP.mono (verifyRhs_ok h2) fun t ⟨rt, ft, et⟩ => ⟨?_, ?_, ?_⟩
    · exact (h1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans (rt.mono (by decide)))
    · exact hf1.trans ((f2.mono (by simp)).trans (ft.mono (by simp)))
    · have hk2 : ∀ o, 7776 ≤ o → o + 128 ≤ 8032 → tableAt s2.mem b o = tableAt s1.mem b o := fun o ho ho' =>
        tableAt_keep f2 fun r hr => by
          have hB : BITSB = 32 := rfl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
          · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
          · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
          · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
          · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
      rw [et, t2, hk2 7904 (by decide) (by decide), hk2 7776 (by decide) (by decide), ta, tr,
        bytesAt_ws f2 (sideW_sub (by decide)) h1.ctx.chD (by decide),
        bytesAt_ws h1.frame decW_sub h.chD (by decide),
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
      have hf : eqResult s.mem pk sig ch = false := by
        unfold eqResult
        simp only [inPtr, ↓reduceIte, Nat.one_ne_zero] at hno
        revert hno
        cases Spec.Ed25519.decodePoint (bytesAt s.mem pk 32) <;>
          cases Spec.Ed25519.decodePoint (bytesAt s.mem sig 32) <;> simp
      rw [hf]; rfl

/-- **The verification's body**: `verifyEquation` of the inputs, in `s3`. -/
theorem verifyBody_ok {s : State} (h : VCtx b pk sig ch s) :
    WP isa verifyBody s fun t => Rest verR s t ∧ Frame (verW b) s.mem t.mem ∧
      t.gpr .s3 = if Spec.Ed25519.verifyEquation (bytesAt s.mem pk 32) (bytesAt s.mem sig 64)
        (bytesAt s.mem ch 64) then 1 else 0 := by
  unfold verifyBody
  refine WP.seq (WP.mono (verifyScalar_ok h) fun s1 ⟨r1, f1, h8⟩ => ?_)
  rw [verifyEquation_eq]
  have hv1 : VCtx b pk sig ch s1 := h.of_rest r1 (by decide)
  have hF : ∀ r ∈ [FA b], r ∈ verW b := by simp
  refine WP.ite (s1.gpr .a5 == 0) (eval_zero s1 .a5) (fun hz => ?_) (fun hz => ?_)
  · have hlt := h8.mp (beq_iff_eq.mp hz)
    refine WP.seq (WP.mono (initFields_ok hv1.ctx.ctx) fun s2 ⟨r2, f2⟩ => ?_)
    refine WP.mono (verifyDecode_ok (hv1.of_rest r2 (by decide))) fun t ⟨rt, ft, et⟩ => ⟨?_, ?_, ?_⟩
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
