module

public import VerifiedGarbage.Proof.Dsa.Arm.Body
public import VerifiedGarbage.Proof.Dsa.Arm.Shape
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA on 32-bit ARM: choosing the widths, and rejecting a domain

`widthDispatch_ok` follows the public widths in the header to the code
for them (`sized`); `sized_ok` runs the shape check and then either the
body or the failure, which zeroes the output when signing (`failure_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_movw wp_cmp wp_dp wp_strb op2_imm op2_reg dpVal eval_eq eval_ne)
open VG.Proof.Zeroize (Prefix prefix_writeW prefix_spec)

/-! ## The widths -/

theorem cmp_word {x : BitVec 32} {w : Nat} (hw : w < 2 ^ 32) :
    (x - BitVec.ofNat 32 w == 0) = decide (x.toNat = w) := by
  have h := cmp_ofNat (a := x.toNat) (b := w) x.isLt hw
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h

/-- One width of the header against a constant. -/
theorem matchOne_ok {s : State} {base : Addr} {size d w : Nat} (hs : Ws s base size) (hd : d < 4096)
    (hd' : d + 4 ≤ size) (hw : w < 2 ^ 16) :
    WP isa (.block [.ldr .r4 .r12 d, .movw .r5 (BitVec.ofNat 16 w), .cmp .r4 (.reg .r5)]) s fun t =>
      t.z = decide ((hdr base s d).toNat = w) ∧ Rest [.r4, .r5] s t ∧ t.mem = s.mem :=
  wp_ldr12 hs hd hd' fun u₁ v₁ => wp_movw fun u₂ v₂ => wp_cmp (op2_reg _ _) fun t f z => WP.block_nil
    ⟨by rw [z, v₂.gpr, v₂.other .r4 (by decide), v₁.gpr, movw_ofNat hw, cmp_word (by omega)],
      ((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (f.rest _), by rw [f.mem, v₂.mem, v₁.mem]⟩

theorem widthMatch_ok {s : State} {base : Addr} {size pLen qLen wp wq : Nat} (hs : Ws s base size)
    (hz : 120 ≤ size) (hp : (hdr base s 100).toNat = pLen) (hq : (hdr base s 104).toNat = qLen)
    (bp : wp < 2 ^ 16) (bq : wq < 2 ^ 16) :
    WP isa (Entry.widthMatch wp wq) s fun t =>
      t.z = decide (pLen = wp ∧ qLen = wq) ∧ Rest [.r4, .r5] s t ∧ t.mem = s.mem := by
  unfold Entry.widthMatch
  refine WP.seq (WP.mono (matchOne_ok (d := 100) hs (by decide) (by omega) bp) fun u ⟨Z, R, M⟩ => ?_)
  rw [hp] at Z
  refine WP.ite u.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
  · have P : pLen = wp := of_decide_eq_true (Z ▸ ht)
    refine WP.mono (matchOne_ok (d := 104) (hs.of_rest R (by decide)) (by decide) (by omega) bq)
      fun t ⟨Z₂, R₂, M₂⟩ => ⟨?_, R.trans R₂, M₂.trans M⟩
    rw [Z₂, show hdr base u 104 = hdr base s 104 by simp only [hdr, M], hq]
    simp [P]
  · have P : ¬ pLen = wp := of_decide_eq_false (Z ▸ hf)
    refine wp_mov (op2_imm (by decide)) fun u₁ v₁ => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil
      ⟨?_, (R.trans (v₁.rest (by decide))).trans (f.rest _), by rw [f.mem, v₁.mem, M]⟩
    rw [z, v₁.gpr]
    simp [P]

theorem widthDispatch_ok (signing : Bool) (widths : List (Nat × Nat))
    {s : State} {base : Addr} {size pLen qLen : Nat} {Q : State → Prop}
    (hs : Ws s base size) (hz : 120 ≤ size) (member : (pLen, qLen) ∈ widths)
    (bound : ∀ w ∈ widths, w.1 < 2 ^ 16 ∧ w.2 < 2 ^ 16)
    (hp : (hdr base s 100).toNat = pLen) (hq : (hdr base s 104).toNat = qLen)
    (body : ∀ t, Rest [.r4, .r5] s t → t.mem = s.mem → WP isa (Entry.sized signing pLen qLen) t Q) :
    WP isa (Entry.widthDispatch signing widths) s Q := by
  induction widths generalizing s with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    obtain ⟨wp, wq⟩ := w
    have B := bound (wp, wq) List.mem_cons_self
    unfold Entry.widthDispatch
    refine WP.seq (WP.mono (widthMatch_ok hs hz hp hq B.1 B.2) fun t ⟨Z, R, M⟩ => ?_)
    refine WP.ite t.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
    · have Both : pLen = wp ∧ qLen = wq := of_decide_eq_true (Z ▸ ht)
      rw [← Both.1, ← Both.2]
      exact body t R M
    · have Both : ¬ (pLen = wp ∧ qLen = wq) := of_decide_eq_false (Z ▸ hf)
      refine ih (hs.of_rest R (by decide))
        (by simpa only [List.mem_cons, Prod.mk.injEq, Both, false_or] using member)
        (fun w hw => bound w (List.mem_cons_of_mem _ hw))
        (by simp only [hdr, M]; exact hp) (by simp only [hdr, M]; exact hq)
        fun u Ru Mu => body u (R.trans Ru) (Mu.trans M)

/-! ## The domain's shape -/

theorem sized_ok (signing : Bool) {s : State} {base : Addr} {size pLen qLen nP nQ P Q : Nat}
    {post : State → Prop} (hs : Ws s base size) (hz : 4960 ≤ size) (wp : Width pLen nP) (wq : Width qLen nQ)
    (Rp : Ready s base (.input .p) pLen) (Rq : Ready s base (.input .q) qLen)
    (hP : operand base s (.input .p) pLen = P) (hQ : operand base s (.input .q) qLen = Q)
    (failure : ∀ t, ¬ shapeValid P Q → Rest coreClob s t → Outs base shapeRanges s.mem t.mem →
      WP isa (Entry.failure signing) t post)
    (body : ∀ t, shapeValid P Q → maskW base t = BitVec.allOnes 32 →
      (hdr base t 112).toNat = min (hdr base s 108).toNat (qWidth Q) →
      Rest coreClob s t → Outs base shapeRanges s.mem t.mem →
      WP isa (if signing then SignVerify.signBody pLen qLen else SignVerify.verifyBody pLen qLen) t post) :
    WP isa (Entry.sized signing pLen qLen) s post := by
  unfold Entry.sized
  refine WP.seq (WP.mono (check_ok hs hz wp wq Rp Rq hP hQ) fun t ⟨Z, M, D, R, O⟩ => ?_)
  refine WP.ite t.z (eval_eq _) (fun ht => failure t (of_decide_eq_true (Z ▸ ht)) R O) (fun hf => ?_)
  have V : shapeValid P Q := Classical.not_not.mp (of_decide_eq_false (Z ▸ hf))
  exact body t V (by rw [M]; simp [mask32, V]) D R O

/-! ## Rejection -/

/-- A zero byte of the output. -/
theorem failureStep_ok {s : State} {out : BitVec 32} {len i : Nat}
    (hi : i < len) (hf : out.toNat + len ≤ 2 ^ 32) (hl : len < 2 ^ 32)
    (hp : s.gpr .r11 = out + BitVec.ofNat 32 i) (he : s.gpr .lr = out + BitVec.ofNat 32 len) (hz : s.gpr .r4 = 0)
    (hw : InRegions s.wr (State.addr out + BitVec.ofNat 64 i) 1)
    (zeroed : Prefix s.mem (State.addr out) i) :
    WP isa (.block [.strb .r4 .r11 0, .dp .add .r11 .r11 (.imm 1), .cmp .r11 (.reg .lr)]) s fun t =>
      t.gpr .r11 = out + BitVec.ofNat 32 (i + 1) ∧ t.gpr .lr = s.gpr .lr ∧ t.gpr .r4 = 0 ∧
      t.z = decide (i + 1 = len) ∧ Prefix t.mem (State.addr out) (i + 1) ∧
      Outside (State.addr out) 0 len s.mem t.mem ∧ Rest [.r11] s t := by
  have ea : State.addr (s.gpr .r11 + BitVec.ofNat 32 0) = State.addr out + BitVec.ofNat 64 i := by
    rw [hp, Offset.add_add, Nat.add_zero, VG.Arm.addr_add (by omega)]
  refine wp_strb (by decide) ea hw fun u₁ m₁ => wp_dp (op2_imm (by decide)) fun u₂ v₂ =>
    wp_cmp (op2_reg _ _) fun t f z => WP.block_nil ?_
  have r11 : u₂.gpr .r11 = out + BitVec.ofNat 32 (i + 1) := by
    rw [v₂.gpr, dpVal, m₁.gpr, hp]
    show out + BitVec.ofNat 32 i + BitVec.ofNat 32 1 = _
    rw [Offset.add_add]
  have lr : u₂.gpr .lr = s.gpr .lr := by rw [v₂.other .lr (by decide), m₁.gpr]
  have mt : t.mem = s.mem.writeW (State.addr out + BitVec.ofNat 64 i) (BitVec.setWidth 8 (0 : BitVec 32)) := by
    rw [f.mem, v₂.mem, m₁.mem, hz]
  refine ⟨by rw [f.gpr, r11], by rw [f.gpr, lr], by rw [f.gpr, v₂.other .r4 (by decide), m₁.gpr, hz], ?_, ?_, ?_,
    ((m₁.rest _).trans (v₂.rest (by decide))).trans (f.rest _)⟩
  · rw [z, r11, lr, he, sub_add_add, cmp_ofNat (by omega) (by omega)]
  · rw [mt, show BitVec.setWidth 8 (0 : BitVec 32) = (0 : BitVec 8) from rfl]
    exact prefix_writeW (w := 8) zeroed (by omega)
  · rw [mt]
    exact (writeW8_outside s.mem (State.addr out) (d := i) _ (by omega)).mono (Nat.zero_le _) (by omega)

theorem failureLoop_ok {s : State} {out : BitVec 32} {len : Nat} (h0 : 0 < len) (hf : out.toNat + len ≤ 2 ^ 32) (hl : len < 2 ^ 32)
    (hp : s.gpr .r11 = out) (he : s.gpr .lr = out + BitVec.ofNat 32 len) (hz : s.gpr .r4 = 0)
    (hw : ∀ i < len, InRegions s.wr (State.addr out + BitVec.ofNat 64 i) 1) :
    WP isa (.loop (.block [.strb .r4 .r11 0, .dp .add .r11 .r11 (.imm 1), .cmp .r11 (.reg .lr)]) .ne) s fun t =>
      Prefix t.mem (State.addr out) len ∧ Outside (State.addr out) 0 len s.mem t.mem ∧ Rest [.r11] s t := by
  refine WP.loop (M := isa) (fun k (u : State) => ∃ i, k = len - i ∧ i < len ∧
      u.gpr .r11 = out + BitVec.ofNat 32 i ∧ u.gpr .lr = out + BitVec.ofNat 32 len ∧ u.gpr .r4 = 0 ∧
      Prefix u.mem (State.addr out) i ∧ Outside (State.addr out) 0 len s.mem u.mem ∧ Rest [.r11] s u) ?_ len s
    ⟨0, by omega, h0, by rw [hp]; exact (BitVec.add_zero _).symm, he, hz, fun j hj => absurd hj (Nat.not_lt_zero _),
      Outside.refl _ _ _ _, Rest.refl _ _⟩
  rintro k u ⟨i, rfl, hi, Pu, Eu, Zu, Bu, Ou, Ru⟩
  refine WP.mono (failureStep_ok hi hf hl Pu Eu Zu (by rw [Ru.wr]; exact hw i hi) Bu)
    fun t ⟨Pt, Et, Zt, zt, Bt, Ot, Rt⟩ => ?_
  by_cases d : i + 1 = len
  · exact .inl ⟨by rw [eval_ne, zt]; simp [d], d ▸ Bt, Ou.trans Ot, Ru.trans Rt⟩
  · exact .inr ⟨by rw [eval_ne, zt]; simp [d], len - (i + 1), by omega, i + 1, rfl, by omega, Pt, by rw [Et, Eu],
      Zt, Bt, Ou.trans Ot, Ru.trans Rt⟩

/-- Signing's failure: zeros in the output and 0 in `r0`. -/
theorem failure_ok {s : State} {base : Addr} {size qLen : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    (O : Output s base size (2 * qLen)) (hq : (hdr base s 104).toNat = qLen) (q0 : 0 < qLen) (q32 : qLen ≤ 32) :
    WP isa (Entry.failure true) s fun t =>
      t.gpr .r0 = 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr (pointerValue base s (.input .out))) (2 * qLen) =
        List.replicate (2 * qLen) 0 ∧
      Rest [.r0, .r4, .r11, .lr] s t ∧
      Outside (State.addr (pointerValue base s (.input .out))) 0 (2 * qLen) s.mem t.mem := by
  have hf := O.fits
  simp only [Entry.failure, ↓reduceIte, Core.sequence, List.foldr]
  refine WP.seq (wp_ldr12 hs (d := 96) (by decide) (by omega) fun u₁ v₁ => ?_)
  refine wp_ldr12 (hs.of_upd v₁ (by decide)) (d := 104) (by decide) (by omega) fun u₂ v₂ => ?_
  refine wp_dp (op2_reg _ _) fun u₃ v₃ => wp_dp (op2_reg _ _) fun u₄ v₄ => wp_mov (op2_imm (by decide))
    fun u₅ v₅ => WP.block_nil ?_
  have out : u₅.gpr .r11 = pointerValue base s (.input .out) := by
    rw [v₅.other .r11 (by decide), v₄.other .r11 (by decide), v₃.other .r11 (by decide),
      v₂.other .r11 (by decide), v₁.gpr]; rfl
  have q : u₂.gpr .r4 = BitVec.ofNat 32 qLen := by
    rw [v₂.gpr, show hdr base u₁ 104 = hdr base s 104 by simp only [hdr, v₁.mem], ← hq, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have lr : u₅.gpr .lr = pointerValue base s (.input .out) + BitVec.ofNat 32 (2 * qLen) := by
    rw [v₅.other .lr (by decide), v₄.gpr, dpVal, v₃.gpr, dpVal, v₃.other .r4 (by decide), q,
      v₂.other .r11 (by decide), v₁.gpr, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.two_mul]
    rfl
  have R₅ : Rest [.r0, .r4, .r11, .lr] s u₅ :=
    ((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (v₃.rest (by decide))).trans
      (v₄.rest (by decide))).trans (v₅.rest (by decide))
  have M₅ : u₅.mem = s.mem := by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  refine WP.seq (WP.mono (failureLoop_ok (by omega) hf (by omega) out lr v₅.gpr
    (fun i hi => by rw [R₅.wr]; exact O.writes i 1 (by omega))) fun t ⟨B, Ot, Rt⟩ => ?_)
  refine WP.seq (wp_mov (op2_imm (by decide)) fun t' v => WP.block_nil (WP.block_nil ⟨v.gpr, ?_, ?_, ?_⟩))
  · rw [v.mem]; exact prefix_spec B
  · exact (R₅.trans (Rt.mono (by decide))).trans (v.rest (by decide))
  · rw [v.mem, ← M₅]; exact Ot

end VG.Proof.Dsa.Arm
