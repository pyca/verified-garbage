module

public import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
public import VerifiedGarbage.Proof.Bignum.Arm.Stack
public import VerifiedGarbage.Proof.Rsa.Arm.KcStart
public import VerifiedGarbage.Proof.Framework.CallLay
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: the stage of the candidates

`MM P s`: Montgomery multiplication ready but for `r0`, `n` in its array 0
and `R² mod n` in its array 4. Steps of the key working space that write
neither the key arrays 16–20 nor 24 keep it (`MM.of_keep`). The frame's
words are those the body started with (`Bs.fw`), and loads of them
(`Bs.ldrSp`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

structure MM (P : RP) (s : State) : Prop where
  mr : MR P s
  n0 : numAt s.mem (State.addr P.M0) P.w6 0 = P.n
  r2 : numAt s.mem (State.addr P.M0) P.w6 4 = 2 ^ (128 * P.w6) % P.n

/-- A step that writes no key array 16–20 or 24 keeps `MM`. -/
theorem MM.of_keep {P : RP} {σ s t : State} (h : MM P s) (hb : Bs P σ s) {js ds : List Nat}
    (k : Keep P.B P.w js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < 16 ∨ mBase < j ∧ j < nArr ∧ j ≠ mR2)
    (hds : ∀ d ∈ ds, d + 4 ≤ hdr) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MM P t := by
  have pre := hb.pre
  have sz := pre.sizes
  have hf := pre.fS
  have hZ := Z_64 sz
  have fits := sz.fits
  have keepNum : ∀ i, i = 0 ∨ i = 4 →
      numAt t.mem (State.addr P.M0) P.w6 i = numAt s.mem (State.addr P.M0) P.w6 i := by
    intro i hi
    rw [numAt_val32 sz hf, numAt_val32 sz hf]
    have hS : S P.w = 4 * (P.w + 2) := rfl
    have ww : P.w = 2 * P.w6 + 2 := rfl
    have fi : arr P.w (mBase + i) + S P.w ≤ P.Z := fitZ_w sz (by rcases hi with rfl | rfl <;> decide)
    refine k.val32 (fun r hr => ?_) (by omega)
    simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨j, hj, rfl⟩ | ⟨d', hd', rfl⟩
    · have hji : j ≠ mBase + i := by
        rcases hjs j hj with c | ⟨c, _, c'⟩ <;> rcases hi with rfl | rfl <;> simp [mBase, mR2] at * <;> omega
      have := arr_disj (w := P.w) hji
      dsimp only; omega
    · have := hds d' hd'
      have : hdr ≤ arr P.w (mBase + i) := Nat.le_add_right _ _
      dsimp only; omega
  exact ⟨h.mr.of_keep hb k (fun j hj => (hjs j hj).imp_right fun c => ⟨c.1, c.2.1⟩) hds sp rd wr,
    (keepNum 0 (.inl rfl)).trans h.n0, (keepNum 4 (.inr rfl)).trans h.r2⟩

/-! ## The frame -/

/-- A frame word but word 0. -/
theorem Bs.fwEq {P : RP} {σ s : State} (h : Bs P σ s) {o : Nat} (ho : 4 ≤ o) (ho' : o + 4 ≤ 88) :
    fw s.mem P o = fw σ.mem P o := by
  have pre := h.pre
  refine h.frame.readW (r := ⟨off (State.addr P.sp) o, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact pre.sF.symm.sub_left (Offset.sub_base _ ho')
  · exact Offset.disjoint_base _ ho (by omega)

/-- `ldr t, [sp, #o]` of a frame word but word 0. -/
theorem Bs.ldrSp {P : RP} {σ s : State} (h : Bs P σ s) {o : Nat} (ho : 4 ≤ o) (ho' : o + 4 ≤ 88)
    (h4 : o % 4 = 0) {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (fw σ.mem P o) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q := by
  have pre := h.pre
  have spf := pre.spFit
  have ea : State.addr (s.sp + BitVec.ofNat 32 o) = off (State.addr P.sp) o := by
    rw [h.sp, pre.sp]; exact addr_add (by omega)
  refine wp_loadStack (by omega) ea ?_ fun s' u => k s' (by rw [← h.fwEq ho ho']; exact u)
  rw [h.rd, h.wr]
  rcases (by omega : o + 4 ≤ 56 ∨ 56 ≤ o) with c | c
  · exact ⟨⟨State.addr P.sp, 56⟩, List.mem_append_right _ (by rw [pre.wr]; simp),
      Offset.contains_base _ c (by omega)⟩
  · have read := CallLay.inRegions_sub pre.rdA (off := o - 56) (l := 4) (by omega) (by decide)
    rwa [show off (State.addr P.sp) 56 + BitVec.ofNat 64 (o - 56) = off (State.addr P.sp) o by
      simp only [off]; rw [Offset.add_add]; congr 2; omega] at read

end VG.Proof.Rsa.Arm.Recover
