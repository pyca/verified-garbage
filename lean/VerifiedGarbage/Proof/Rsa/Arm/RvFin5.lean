module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFin4
import VerifiedGarbage.Proof.Rsa.Arm.RvStore
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint4
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.WideMul

/-! # `vg_rsa_recover_primes` on ARMv7: the factors written out (`stores_vp`)

`Bo P σ s`: what the end of the body keeps of `σ`, memory but in the working
space, frame word 0 and the outputs `p` and `q`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)

structure Bo (P : RP) (σ s : State) : Prop where
  pre : In P σ
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame [P.rS, P.r0F, P.rP, P.rQ] σ.mem s.mem

theorem Bs.bo {P : RP} {σ s : State} (h : Bs P σ s) : Bo P σ s :=
  ⟨h.pre, h.sp, h.rd, h.wr, h.frame.mono (by simp)⟩

/-- A frame word but word 0. -/
theorem Bo.fwEq {P : RP} {σ s : State} (h : Bo P σ s) {o : Nat} (ho : 4 ≤ o) (ho' : o + 4 ≤ 88) :
    fw s.mem P o = fw σ.mem P o := by
  have pre := h.pre
  refine h.frame.readW (r := ⟨off (State.addr P.sp) o, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pre.sF.symm.sub_left (Offset.sub_base _ ho')
  · exact Offset.disjoint_base _ ho (by omega)
  · exact pre.pF.symm.sub_left (Offset.sub_base _ ho')
  · exact pre.qF.symm.sub_left (Offset.sub_base _ ho')

/-- `ldr t, [sp, #o]` of a frame word but word 0. -/
theorem Bo.ldrSp {P : RP} {σ s : State} (h : Bo P σ s) {o : Nat} (ho : 4 ≤ o) (ho' : o + 4 ≤ 88)
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

/-- Memory of the working space through a step that writes only `R`. -/
theorem w32_frame {P : RP} {m m' : Mem} {R : Region} (f : Frame [R] m m') (hR : R.Disjoint P.rS)
    (hZ : P.Z ≤ 2 ^ 64) {d : Nat} (hd : d + 4 ≤ P.Z) : w32 m' (State.addr P.B) d = w32 m (State.addr P.B) d := by
  simp only [w32]
  rw [f.readW (r := P.rS) (Offset.contains_base _ hd (by omega)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR.symm) (by decide)]

theorem num_frame {P : RP} {m m' : Mem} {R : Region} (f : Frame [R] m m') (hR : R.Disjoint P.rS)
    (sz : Sizes P) {j : Nat} (hj : j < nArr) : num m' P.B P.w j = num m P.B P.w j := by
  have fz := fitZ_w sz hj
  have hS : S P.w = 4 * (P.w + 2) := rfl
  exact val32_congr fun i hi => w32_frame f hR (Z_64 sz) (by omega)

/-- The outputs. -/
abbrev outP (P : RP) (σ : State) : List Byte :=
  if okF P σ then Spec.Rsa.i2osp (bigF P σ) P.K else List.replicate P.K 0
abbrev outQ (P : RP) (σ : State) : List Byte :=
  if okF P σ then Spec.Rsa.i2osp (smallF P σ) P.K else List.replicate P.K 0

/-- The end of the body with the factors found or not. -/
abbrev Fe (P : RP) (E : State → Prop) (σ s : State) : Prop :=
  E σ ∧ Bo P σ s ∧ Spec.Rsa.bytesAt s.mem (State.addr P.pP) P.K = outP P σ ∧
    Spec.Rsa.bytesAt s.mem (State.addr P.qP) P.K = outQ P σ ∧ s.gpr .r0 = BitVec.ofNat 32 (b2n (okF P σ))

section
variable {P : RP}

theorem big_lt {σ : State} (pre : In P σ) (hn0 : 0 < P.n) : bigF P σ < 2 ^ (8 * P.K) := by
  have := bytes_lt σ.mem (State.addr P.nP) P.K
  rw [pre.nB] at this
  have hn : P.n < 2 ^ (8 * P.K) := this
  have h1 : pF P σ ≤ P.n := Nat.gcd_le_right _ hn0
  have h2 : qF P σ ≤ P.n := Nat.div_le_self _ _
  simp only [bigF]; omega

theorem small_lt {σ : State} (pre : In P σ) (hn0 : 0 < P.n) : smallF P σ < 2 ^ (8 * P.K) := by
  exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _)) (big_lt pre hn0)

/-- After `p`. -/
abbrev Fs1 (P : RP) (E : State → Prop) (σ s : State) : Prop :=
  E σ ∧ Bo P σ s ∧ Ws s P.B P.Z P.w nArr ∧ slot s.mem P.B sMask = b2n (okF P σ) ∧
    num s.mem P.B P.w 6 = smallF P σ ∧ Spec.Rsa.bytesAt s.mem (State.addr P.pP) P.K = outP P σ

theorem storeP_vp (hn0 : 0 < P.n) {E : State → Prop} :
    VP (fun σ s => Fo P E σ s ∧ s.gpr .r10 = P.pP ∧ s.gpr .r11 = BitVec.ofNat 32 P.K)
      (VG.Impl.Rsa.Arm.CrtValues.store 5) (Fs1 P E) := by
  refine VP.taint [.r7, .r8, .r9, .r10, .r11] storeP_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨⟨e, h, hw⟩, p10, p11⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
    · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
    · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
  have pre := h.bs.pre
  have sz := pre.sizes
  have kw := sz.kw
  have vM : slot s.mem P.B sMask = b2n (okF P σ) := by rw [h.sl sMask (by simp)]; simp [upd]
  have vM' : slot s.mem P.B VG.Impl.Rsa.Arm.CrtValues.sMask = b2n (okF P σ) := vM
  refine WP.mono (store_ok' hw (Z := P.Z) (w := P.w) (dst := P.pP) (k := P.K) (j := 5) (R := P.rP) (by decide) (by decide) pre.sP.symm
    (by rw [h.bs.wr, pre.wr]; simp) rfl (by have := pre.k1; omega) (by omega) pre.fP p10 p11
    (by rw [vM']; exact VG.Proof.Rsa.b2n_le _) (Nat.le_trans (by decide) (hdr_Z sz)))
    fun t ⟨hwt, bt, ft, rt⟩ => ⟨e, ⟨pre, rt.sp.trans h.bs.sp, rt.rd.trans h.bs.rd, rt.wr.trans h.bs.wr,
      (h.bs.frame.mono (by simp)).trans (ft.mono (by simp))⟩, hwt, ?_, ?_, ?_⟩
  · rw [← vM]; exact w32_frame ft pre.sP.symm (Z_64 sz) (Nat.le_trans (by decide) (hdr_Z sz))
  · rw [num_frame ft pre.sP.symm sz (by decide), h.arrs 6 (by simp)]; simp [upd]
  · rw [bt, vM', h.arrs 5 (by simp)]
    have e5 : upd (upd (fun _ => 0) 5 (bigF P σ)) 6 (smallF P σ) 5 = bigF P σ := by simp [upd]
    dsimp only
    rw [e5, Nat.mod_eq_of_lt (big_lt pre hn0)]
    simp only [outP]
    cases okF P σ <;> simp [b2n]

theorem storeQ_vp (hn0 : 0 < P.n) {E : State → Prop} :
    VP (fun σ s => Fs1 P E σ s ∧ s.gpr .r10 = P.qP ∧ s.gpr .r11 = BitVec.ofNat 32 P.K)
      (VG.Impl.Rsa.Arm.CrtValues.store 6) (fun σ s => E σ ∧ Bo P σ s ∧ Ws s P.B P.Z P.w nArr ∧
        slot s.mem P.B sMask = b2n (okF P σ) ∧ Spec.Rsa.bytesAt s.mem (State.addr P.pP) P.K = outP P σ ∧
        Spec.Rsa.bytesAt s.mem (State.addr P.qP) P.K = outQ P σ) := by
  refine VP.taint [.r7, .r8, .r9, .r10, .r11] storeQ_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨⟨e, h, hw, vM, v6, bp⟩, p10, p11⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · rw [h₁.1.2.2.1.r7, h₂.1.2.2.1.r7]
    · rw [h₁.1.2.2.1.r8, h₂.1.2.2.1.r8]
    · rw [h₁.1.2.2.1.r9, h₂.1.2.2.1.r9]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
  have pre := h.pre
  have sz := pre.sizes
  have kw := sz.kw
  have vM' : slot s.mem P.B VG.Impl.Rsa.Arm.CrtValues.sMask = b2n (okF P σ) := vM
  refine WP.mono (store_ok' hw (Z := P.Z) (w := P.w) (dst := P.qP) (k := P.K) (j := 6) (R := P.rQ) (by decide) (by decide)
    pre.sQ.symm (by rw [h.wr, pre.wr]; simp) rfl (by have := pre.k1; omega) (by omega) pre.fQ p10 p11
    (by rw [vM']; exact VG.Proof.Rsa.b2n_le _) (Nat.le_trans (by decide) (hdr_Z sz)))
    fun t ⟨hwt, bt, ft, rt⟩ => ⟨e, ⟨pre, rt.sp.trans h.sp, rt.rd.trans h.rd, rt.wr.trans h.wr,
      h.frame.trans (ft.mono (by simp))⟩, hwt, ?_, ?_, ?_⟩
  · rw [← vM]; exact w32_frame ft pre.sQ.symm (Z_64 sz) (Nat.le_trans (by decide) (hdr_Z sz))
  · rw [VG.Proof.Rsa.Arm.CrtValues.bytes_frame ft (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact pre.pQ) (by have := pre.k2; omega), bp]
  · rw [bt, vM', v6, Nat.mod_eq_of_lt (small_lt pre hn0)]
    simp only [outQ]
    cases okF P σ <;> simp [b2n]

theorem Bo.of_upd {σ s t : State} (h : Bo P σ s) {r : Reg} {v : BitVec 32} (u : Upd s t r v) : Bo P σ t :=
  ⟨h.pre, u.sp.trans h.sp, u.rd.trans h.rd, u.wr.trans h.wr, u.mem ▸ h.frame⟩

/-- The factors written out, and the mask returned. -/
theorem stores_vp (hn0 : 0 < P.n) {E : State → Prop} : VP (Fo P E) stores (Fe P E) := by
  simp only [stores, seqs]
  refine VP.seq (G := fun σ s => Fo P E σ s ∧ s.gpr .r10 = P.pP ∧ s.gpr .r11 = BitVec.ofNat 32 P.K) ?_
    (VP.seq (storeP_vp hn0) (VP.seq (G := fun σ s => Fs1 P E σ s ∧ s.gpr .r10 = P.qP ∧
      s.gpr .r11 = BitVec.ofNat 32 P.K) ?_ (VP.seq (storeQ_vp hn0) ?_)))
  · show VP _ (.block ([(Reg.r10, oP), (Reg.r11, aoK)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.bs.sp, h₁.2.1.bs.pre.sp, h₂.2.1.bs.sp, h₂.2.1.bs.pre.sp]
    · refine h.bs.ldrSp (o := oP) (by decide) (by decide) (by decide) fun s1 u1 => ?_
      obtain ⟨h1, hw1⟩ := h.reg hw (u1.rest (ws := [.r10]) (by simp)) u1.mem
      refine h1.bs.ldrSp (o := aoK) (by decide) (by decide) (by decide) fun t u2 => WP.block_nil ?_
      obtain ⟨ht, hwt⟩ := h1.reg hw1 (u2.rest (ws := [.r11]) (by simp)) u2.mem
      exact ⟨⟨e, ht, hwt⟩, by rw [u2.other _ (by decide), u1.gpr, h.bs.pre.wP], by rw [u2.gpr, h.bs.pre.aK]⟩
  · show VP _ (.block ([(Reg.r10, oQ), (Reg.r11, aoK)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw, vM, v6, bp⟩ => ?_
    · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
    · refine h.ldrSp (o := oQ) (by decide) (by decide) (by decide) fun s1 u1 => ?_
      refine (h.of_upd u1).ldrSp (o := aoK) (by decide) (by decide) (by decide) fun t u2 => WP.block_nil ?_
      exact ⟨⟨e, (h.of_upd u1).of_upd u2, (hw.of_upd u1 (by decide) (by decide) (by decide)).of_upd u2 (by decide)
        (by decide) (by decide), by rw [u2.mem, u1.mem]; exact vM, by rw [u2.mem, u1.mem]; exact v6,
        by rw [u2.mem, u1.mem]; exact bp⟩, by rw [u2.other _ (by decide), u1.gpr, h.pre.wQ],
        by rw [u2.gpr, h.pre.aK]⟩
  · refine VP.ctx ret_taint (fun _ _ h => h.2.2.1) fun σ s ⟨e, h, hw, vM, bp, bq⟩ => ?_
    refine wp_ldrSlot hw (d := sMask) (by decide) fun t u => WP.block_nil ⟨e, h.of_upd u, by rw [u.mem]; exact bp,
      by rw [u.mem]; exact bq, ?_⟩
    rw [u.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.Rsa.b2n_le (okF P σ); omega), ← vM]

end

end VG.Proof.Rsa.Arm.Recover
