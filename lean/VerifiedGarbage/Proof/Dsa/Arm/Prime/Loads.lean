module
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Base
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Framework.Arm.Contract

import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.Arm.RvVP
import VerifiedGarbage.Proof.Rsa.Arm.RvKS
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mul

/-! # A candidate on ARMv7: the frame's words, the working space set up, and loads

`Bk P σ s`: what every state of the body keeps of `σ`: memory but `chg`.
Frame words but 0 keep their values (`Bk.fwEq`, `KS.fwEq`). `LS P σ
A s`: the working space with `W` words, `W` in the division's header, and
every array's `W + 2` words holding `A`. `load_okC`: an array read from
octets most significant first.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

structure Bk (P : CP) (σ s : State) : Prop where
  pre : In P σ
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame P.chg σ.mem s.mem

structure LS (P : CP) (σ : State) (A : Nat → Nat) (s : State) : Prop where
  bk : Bk P σ s
  ws : Ws s P.B P.Z P.W nArr
  cnt : slot s.mem P.B 16 = P.W
  full : ∀ j < nArr, val32 s.mem (State.addr P.B) (arr P.W j) (P.W + 2) = A j

/-- A frame word other than 0. -/
abbrev FwOk (o : Nat) : Prop := 4 ≤ o ∧ o + 4 ≤ 88 ∧ o % 4 = 0

section
variable {P : CP} {σ s t : State}

theorem In.rC_eq (pre : In P σ) : P.rC = ⟨State.addr P.sp - BitVec.ofNat 64 56, 56⟩ := by
  show (⟨State.addr (P.sp - BitVec.ofNat 32 56), 56⟩ : Region) = _
  rw [FrameStack.addr_sub' pre.spLo]

/-- A frame word but 0 is apart from what the body changes. -/
theorem In.fwSep (pre : In P σ) {o : Nat} (ho : FwOk o) :
    ∀ r ∈ P.chg, Region.Disjoint ⟨off (State.addr P.sp) o, 4⟩ r := by
  have spf := pre.spFit
  intro r hr
  simp only [CP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pre.sF.symm.sub_left (Offset.sub_base _ (by omega))
  · exact pre.uF.symm.sub_left (Offset.sub_base _ (by omega))
  · rw [pre.rC_eq]; exact Offset.disjoint_below _ (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-- A frame word is readable. -/
theorem In.fwRead (pre : In P σ) {o : Nat} (ho' : o + 4 ≤ 88) (h4 : o % 4 = 0) :
    InRegions (σ.rd ++ σ.wr) (off (State.addr P.sp) o) 4 := by
  have spf := pre.spFit
  rcases (by omega : o + 4 ≤ 56 ∨ 56 ≤ o) with c | c
  · exact ⟨⟨State.addr P.sp, 56⟩, List.mem_append_right _ (by rw [pre.wr]; simp),
      Offset.contains_base _ c (by omega)⟩
  · have read := CallLay.inRegions_sub pre.rdA (off := o - 56) (l := 4) (by omega) (by decide)
    rwa [show off (State.addr P.sp) 56 + BitVec.ofNat 64 (o - 56) = off (State.addr P.sp) o by
      simp only [off]; rw [Offset.add_add]; congr 2; omega] at read

theorem Bk.of_rest (h : Bk P σ s) {rs : List Reg} (r : Rest rs s t) (m : t.mem = s.mem) : Bk P σ t :=
  ⟨h.pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, m ▸ h.frame⟩

theorem Bk.of_frame (h : Bk P σ s) (f : Frame P.chg s.mem t.mem) (sp : t.sp = s.sp) (rd : t.rd = s.rd)
    (wr : t.wr = s.wr) : Bk P σ t :=
  ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, h.frame.trans f⟩

theorem Bk.of_upd (h : Bk P σ s) {r : Reg} {v : BitVec 32} (u : Upd s t r v) : Bk P σ t :=
  ⟨h.pre, u.sp.trans h.sp, u.rd.trans h.rd, u.wr.trans h.wr, u.mem ▸ h.frame⟩

theorem Bk.rS_mem (h : Bk P σ s) : P.rS ∈ s.wr := by rw [h.wr]; exact h.pre.rS_mem

theorem KS.bk {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat} (h : KS P σ A live V ls s) :
    Bk P σ s :=
  ⟨h.pre, h.sp, h.rd, h.wr, h.frame⟩

/-- A frame word keeps its value. -/
theorem Bk.fwEq (h : Bk P σ s) {o : Nat} (ho : FwOk o) : fw s.mem P o = fw σ.mem P o :=
  h.frame.readW (r := ⟨off (State.addr P.sp) o, 4⟩) (Region.contains_self _ _) (h.pre.fwSep ho) (by decide)

/-- `ldr t, [sp, #o]` of a frame word whose value `v` is known. -/
theorem Bk.ldrSpV (h : Bk P σ s) {o : Nat} (ho' : o + 4 ≤ 88) (h4 : o % 4 = 0) {v : BitVec 32}
    (hv : fw s.mem P o = v) {t : Reg} {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' t v → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q := by
  have pre := h.pre
  have spf := pre.spFit
  have ea : State.addr (s.sp + BitVec.ofNat 32 o) = off (State.addr P.sp) o := by
    rw [h.sp, pre.sp]; exact addr_add (by omega)
  refine wp_loadStack (by omega) ea ?_ fun s' u => k s' (by rw [← hv]; exact u)
  rw [h.rd, h.wr]
  exact pre.fwRead ho' h4

/-- `ldr t, [sp, #o]` of a frame word but 0. -/
theorem Bk.ldrSp (h : Bk P σ s) {o : Nat} (ho : FwOk o) {t : Reg} {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' t (fw σ.mem P o) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q :=
  h.ldrSpV ho.2.1 ho.2.2 (h.fwEq ho) k

/-- `setupC` after the base and `out_len` are loaded. -/
theorem setupTail_ok (h : Bk P σ s) (r8 : s.gpr .r8 = P.B) (r9 : s.gpr .r9 = BitVec.ofNat 32 P.L) :
    WP isa (.block (([.mov .r9 (.shifted .r9 .lsr 2), .dp .add .r9 .r9 (.imm 2)] : List Instr) ++ stride ++
      ([.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
        .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)] : List Instr))) s fun t =>
      Bk P σ t ∧ Ws t P.B P.Z P.W nArr ∧ slot t.mem P.B 16 = P.W ∧
      t.gpr .r0 = P.B + BitVec.ofNat 32 hdr ∧ t.gpr .lr = BitVec.ofNat 32 (nArr * (P.W + 2)) ∧
      t.gpr .r3 = 0 := by
  have pre := h.pre
  have k1 := pre.k1; have k2 := pre.k2
  have wl := pre.wle
  simp only [List.cons_append, List.append_assoc]
  refine wp_mov (op2_lsr (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  have h9 : s2.gpr .r9 = BitVec.ofNat 32 P.W := by
    rw [u2.gpr, dpVal, u1.gpr, r9]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [CP.W]
    omega
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (by omega) h9 fun s5 h7 r5 m5 => ?_
  have r45 : Rest [.r9, .r7] s s5 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (r5.mono (by simp)))
  have m45 : s5.mem = s.mem := m5.trans (u2.mem.trans u1.mem)
  have ws5 : Ws s5 P.B P.Z P.W nArr :=
    ⟨pre.fS, by rw [r45.wr]; exact h.rS_mem, pre.fits, by simp only [CP.W]; omega, by simp only [CP.W]; omega, h7,
      by rw [r45.gpr _ (by decide), r8], by rw [r5.gpr _ (by decide), h9]⟩
  refine wp_strSlot ws5 (d := 16) (by decide) fun s6 u6 => ?_
  have ws6 := ws5.of_mupd u6
  have o6 := writeW32_outside s5.mem (State.addr P.B) (d := 16) (s5.gpr .r9) (by decide)
  rw [← u6.mem] at o6
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
  refine wp_mul fun s9 u9 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s10 u10 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u11 => WP.block_nil ?_
  have rt : Rest [.r0, .lr, .r3] s6 t := (u7.rest (by simp)).trans ((u8.rest (by simp)).trans
    ((u9.rest (by simp)).trans ((u10.rest (by simp)).trans (u11.rest (by simp)))))
  have mt : t.mem = s6.mem := by rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem]
  have ot : Outside (State.addr P.B) 16 4 s.mem t.mem := by rw [mt, ← m45]; exact o6
  have hz := pre.hdr_Z
  refine ⟨h.of_frame (fun x hx => ot x (.inr ?_)) (by rw [rt.sp, u6.sp, r45.sp]) (by rw [rt.rd, u6.rd, r45.rd])
      (by rw [rt.wr, u6.wr, r45.wr]), ws6.rest rt, ?_, ?_, ?_, by rw [u11.gpr]⟩
  · have := hx _ (List.mem_cons_self)
    simp only [Region.Contains] at this
    simp only [ofs, hdr] at *; omega
  · rw [mt, u6.mem, slot_write_self, ws5.r9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.gpr,
      dpVal, u6.gpr, ws5.r8]
  · rw [u11.other _ (by decide), u10.gpr, u9.gpr, u8.gpr, u8.other _ (by decide), u7.other _ (by decide), u6.gpr,
      ws5.r7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nArr, S]
    rw [Nat.mod_eq_of_lt (a := 65) (by decide), Nat.mod_eq_of_lt (a := 4 * (P.W + 2)) (by omega),
      Nat.mod_eq_of_lt (a := 65 * (4 * (P.W + 2))) (by omega), Nat.mod_eq_of_lt (a := 65 * (P.W + 2)) (by omega)]
    omega

theorem zero_ls (h : Bk P σ s) (hw : Ws s P.B P.Z P.W nArr) (cnt : slot s.mem P.B 16 = P.W)
    (p0 : s.gpr .r0 = P.B + BitVec.ofNat 32 hdr) (plr : s.gpr .lr = BitVec.ofNat 32 (nArr * (P.W + 2)))
    (r3 : s.gpr .r3 = 0) : WP isa VG.Impl.Bignum.Arm.zero s (LS P σ fun _ => 0) := by
  have pre := h.pre
  have fits := pre.fits
  have nfit : hdr + 4 * (nArr * (P.W + 2)) ≤ P.Z := by
    have e : arr P.W nArr = hdr + 4 * (nArr * (P.W + 2)) := by
      show hdr + nArr * (4 * (P.W + 2)) = _; rw [Nat.mul_left_comm]
    rw [← e]; exact fits
  refine WP.mono (zero_ok s (base := P.B) (size := P.Z) (o := hdr) (n := nArr * (P.W + 2))
    ⟨pre.fS, nfit, ⟨P.rS, h.rS_mem, Region.contains_self _ _⟩⟩ (Nat.mul_pos (by decide) (by omega)) p0 plr r3)
    fun t inv => ?_
  refine ⟨h.of_frame (fun x hx => inv.outside x (.inr ?_)) inv.rest.sp inv.rest.rd inv.rest.wr,
    hw.rest inv.rest, ?_, fun j hj => ?_⟩
  · have := hx _ (List.mem_cons_self)
    simp only [Region.Contains] at this
    simp only [ofs] at *; omega
  · rw [← cnt]
    exact inv.outside.w32 (d := 16) (by simp only [hdr]; omega) (by decide)
  · have := VG.Proof.Rsa.Arm.CrtValues.val32_zero_part inv.value (a := j * (P.W + 2)) (c := P.W + 2) (by
      have := Nat.mul_le_mul_right (P.W + 2) (show j + 1 ≤ nArr by omega)
      rw [Nat.succ_mul] at this; omega)
    simpa only [arr, S, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/-- `load j`: array `j`'s `W + 2` words := the `k` bytes at `r4` (`r6 = k`). -/
theorem load_okC (h : Bk P σ s) (hw : Ws s P.B P.Z P.W nArr) {j : Nat}
    (hj : j < nArr) {src : BitVec 32} {k : Nat}
    (rd : InRegions (σ.rd ++ σ.wr) (State.addr src) k) (sepC : ∀ r ∈ P.chg, Region.Disjoint ⟨State.addr src, k⟩ r)
    (fit : src.toNat + k ≤ 2 ^ 32) (hk : 0 < k)
    (hkL : k ≤ P.L) (p4 : s.gpr .r4 = src) (p6 : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (VG.Impl.Rsa.Arm.CrtValues.load j) s fun t => Bk P σ t ∧ Ws t P.B P.Z P.W nArr ∧
      Keep P.B P.W [j] [] s.mem t.mem ∧
      val32 t.mem (State.addr P.B) (arr P.W j) (P.W + 2) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr src) k) ∧
      Rest [.r0, .r1, .r2, .r3, .r5, .lr] s t := by
  have pre := h.pre
  have fa := hw.arr_fit hj
  have nw := hw.nowrap
  have hS : S P.W = 4 * (P.W + 2) := rfl
  have hkw : k ≤ 4 * P.W := by simp only [CP.W]; omega
  have sepS : Region.Disjoint ⟨State.addr src, k⟩ P.rS := sepC _ List.mem_cons_self
  rw [VG.Impl.Rsa.Arm.CrtValues.load, WP.seq_iff]
  refine ptr_ok hw (by decide) (by simp only [nArr] at hj; omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u4 => WP.block_nil ?_
  have rest : Rest [.r0, .r3, .r5, .lr] s u :=
    (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  have mu : u.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, m1]
  have bu := h.of_rest rest mu
  have hu := hw.rest rest
  have ad : State.addr (P.B + BitVec.ofNat 32 (arr P.W j)) = off (State.addr P.B) (arr P.W j) :=
    hw.addr (by omega)
  have p0 : u.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W j) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p1]
  refine WP.mono (loadBE_ok u (src := src) (dst := P.B + BitVec.ofNat 32 (arr P.W j)) (n := P.W + 2)
    hk (by omega) (by omega) fit
    (by rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega)
    (by rw [bu.rd, bu.wr]; exact rd)
    ⟨P.rS, bu.rS_mem, by rw [ad]; exact Offset.contains_base _ (by omega) (by omega)⟩
    (by
      rw [ad]
      refine fun a ha hb => sepS a ha ?_
      exact Region.Contains.byte (r := P.rS) (b := off (State.addr P.B) (arr P.W j)) (n := 4 * (P.W + 2))
        (Offset.contains_base _ (by omega) (by omega)) (by simp only [Region.Contains] at hb; omega))
    p0 (by rw [rest.gpr _ (by decide), p4])
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, p1])
    (by rw [rest.gpr _ (by decide), p6])
    (by rw [u4.other _ (by decide), u3.gpr, dpVal, u2.other .r9 (by decide), r1.gpr .r9 (by decide), hw.r9]
        exact (BitVec.ofNat_add_ofNat (n := 32) P.W 2))
    (by rw [u4.gpr])) ?_
  rintro t ⟨v, f, r⟩
  rw [ad] at f v
  have k : Keep P.B P.W [j] [] u.mem t.mem := VG.Proof.Rsa.Arm.CrtValues.Keep.of_frame_arr f (by omega)
  refine ⟨bu.of_frame (keep_frameC k (by simpa using pre.fitZ hj) (by simp) pre.hdr_Z) r.sp r.rd r.wr,
    hu.rest r, mu ▸ k, ?_, (rest.mono (by simp)).trans (r.mono (by simp))⟩
  rw [VG.Proof.Rsa.Arm.CrtValues.val32_off, Nat.add_zero] at v
  rw [v, mu, VG.Proof.Rsa.Arm.CrtValues.bytes_frame h.frame sepC (by omega)]

end

section
variable {P : CP} {σ s : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.fwEq (h : KS P σ A live V ls s) {o : Nat} (ho : FwOk o) : fw s.mem P o = fw σ.mem P o :=
  h.bk.fwEq ho

theorem KS.ldrSp (h : KS P σ A live V ls s) {o : Nat} (ho : FwOk o) {t : Reg} {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' t (fw σ.mem P o) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q :=
  h.bk.ldrSp ho k

end

end VG.Proof.Dsa.Arm.Prime
