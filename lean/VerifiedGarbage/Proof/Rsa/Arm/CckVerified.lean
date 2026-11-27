module

public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Rsa.Arm.KcFnBase
import VerifiedGarbage.Proof.Rsa.Arm.KcOps
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
public import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheck
import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.Arm.CvFin
import VerifiedGarbage.Proof.Rsa.Arm.CvLoads
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Rsa.Arm.KcFnCT`, which this module and modules that import it used -/

section

/-! ### `Rsa.Arm.KcTaint`, which only this module used -/

section

/-! # The checks of an RSA key on ARMv7: the pieces the taint analysis checks

Between the divisions (whose constant time is `Div.code_ct`), every piece of
the checks computes its addresses and loop counts from the registers given
here, which two runs agree on by correctness: `r8` and `n_len` in `r11` at
the start, `r8` after a division, and `r7`–`r9` otherwise.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck

theorem start_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8, .r11]) start hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ctxDiv_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8]) (.block ctxDiv) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem crtChecks_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) crtChecks hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dChecks1_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) dChecks1 hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dChecks2_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) dChecks2 hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dChecks3_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) dChecks3 hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.KeyCheck

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck

theorem eLoad_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8]) (.block [.ldr .r1 .r8 sE, .ldr .lr .r8 sEl]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem eCmp_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs []) (.block [.cmp .r7 (.imm 1)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ret_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8]) (.block ret) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ret0_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs []) (.block ret0) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.KeyCheck

end

end

/-! ### `Rsa.Arm.KcFn`, which this module and modules that import it used -/

section

/-! ### `Rsa.Arm.KcLoads`, which this module and modules that import it used -/

section

/-! ### `Rsa.Arm.KcEntry`, which only this module used -/

section

/-! # The checks of an RSA key on ARMv7: the entry's first block, and every array zeroed

`EntSt σ s A`: during the entry, the working space's registers are set, `w`
is in the division's header, every array holds `A` (all its `w + 2` words),
and `n` and `n_len` are kept in `r10` and `r11`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys VG.Arm.Spill VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.CrtValues (reg)

section
variable {nA iS : Nat} {ins : List (Nat × Nat)}

structure EntSt (nA iS : Nat) (ins : List (Nat × Nat)) (σ s : State) (A : Nat → Nat) : Prop where
  base : FnBase nA iS ins σ s
  ws : Ws s (geo iS σ).B (geo iS σ).Z (geo iS σ).w nArr
  cnt : s.mem.readW (off (State.addr (geo iS σ).B) 16) 32 = BitVec.ofNat 32 (geo iS σ).w
  full : ∀ j < nArr, val32 s.mem (State.addr (geo iS σ).B) (arr (geo iS σ).w j) ((geo iS σ).w + 2) = A j
  r10 : s.gpr .r10 = σ.gpr .r0
  r11 : s.gpr .r11 = σ.gpr .r1

/-- The registers saved, and where. -/
def saveK : List (Reg × Nat) :=
  [(.r4, 20), (.r5, 24), (.r6, 28), (.r7, 32), (.r8, 36), (.r9, 40), (.r10, 44), (.r11, 48), (.lr, 52),
   (.r2, 56), (.r3, 60)]

theorem entrySave_eq : entrySave = saveK.map (fun p => Instr.str p.1 .r12 p.2) ++
    ([.mov .r8 (.reg .r12), .mov .r10 (.reg .r0), .mov .r11 (.reg .r1), .mov .r4 (.reg .r2),
      .mov .r6 (.reg .r3)] : List Instr) := rfl

theorem saveK_mem {i : Nat} (hi : i < 11) : (savedReg i, 20 + 4 * i) ∈ saveK := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem savedReg_ne {i : Nat} (hi : i < 11) : savedReg i ≠ .r12 := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `ldr r12, [sp, #oS]` and the registers saved. -/
theorem save_ok {σ : State} (h : FnPre nA iS ins σ) (h4 : 4 * iS < 4096) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, FnBase nA iS ins σ t → t.gpr .r12 = (geo iS σ).B → (∀ r, r ≠ .r12 → t.gpr r = σ.gpr r) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.ldrSp .r12 (4 * iS) :: (saveK.map (fun p => Instr.str p.1 .r12 p.2) ++ rest))) σ Q := by
  have fS := h.fS
  have fits := h.fits
  obtain hz : 64 ≤ (stackArg σ (iS + 1)).toNat * 8 := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega_arith) fits
  refine wp_ldrSpA h.rdA h.sp (by have := h.hS; omega_arith) h4 fun s1 u1 => ?_
  refine save_slots_ok (lo := 20) (hi := 64) (by decide) (by rw [u1.gpr]; omega_arith)
    (fun d h1 h2 => ⟨rS iS σ, by rw [u1.wr, h.wr]; simp, by
      rw [u1.gpr]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) ?_
  refine k _ ⟨h, u1.sp, u1.rd, u1.wr, ?_, fun i hi => ?_⟩ u1.gpr
    (fun r hr => u1.other r hr)
  · rw [u1.gpr]
    refine Frame.sub (rs := [⟨State.addr (stackArg σ iS), 64⟩]) ?_ fun r hr => ⟨rS iS σ, by simp, ?_⟩
    · rw [← u1.mem]
      exact saveMem_frame _ _ _ (by decide) _ (by decide)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by omega_arith)
  · have sv := saveMem_saved (lo := 20) (hi := 64) (State.addr (s1.gpr .r12)) s1.gpr s1.mem saveK (by decide)
      _ (saveK_mem hi)
    simp only [u1.gpr] at sv
    show ((saveMem s1.mem (State.addr (s1.gpr .r12)) s1.gpr saveK).readW
      (off (State.addr (stackArg σ iS)) (20 + 4 * i)) 32).toNat = _
    rw [u1.gpr]
    erw [sv]
    rw [u1.other _ (savedReg_ne hi)]

/-- The entry's first block and `zero`: every array zero. -/
theorem entryFirst_ok {σ : State} (h : FnPre nA iS ins σ) (h4 : 4 * iS < 4096) :
    WP isa (seqs [.block (([.ldrSp .r12 (4 * iS)] : List Instr) ++ entrySave ++ setup), zero]) σ fun t =>
      EntSt nA iS ins σ t (fun _ => 0) ∧ t.gpr .r4 = σ.gpr .r2 ∧ t.gpr .r6 = σ.gpr .r3 := by
  have w16 := h.w16
  have kb := h.kb
  have fits := h.fits
  have fS := h.fS
  rw [wp_seqs_cons (List.cons_ne_nil _ _), entrySave_eq]
  simp only [List.cons_append, List.append_assoc]
  refine save_ok h h4 fun s1 b1 p12 o1 => ?_
  simp only [List.nil_append]
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_mov (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun s5 u5 => ?_
  refine wp_mov (op2_reg _ _) fun s6 u6 => ?_
  obtain r6' : Rest [.r8, .r10, .r11, .r4, .r6] s1 s6 := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans
    ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp)))))
  obtain m6 : s6.mem = s1.mem := u6.mem.trans (u5.mem.trans (u4.mem.trans (u3.mem.trans u2.mem)))
  obtain b6 := b1.of_rest r6' m6
  obtain e8 : s6.gpr .r8 = (geo iS σ).B := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
      p12]
  obtain e10 : s6.gpr .r10 = σ.gpr .r0 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide),
      o1 _ (by decide)]
  obtain e11 : s6.gpr .r11 = σ.gpr .r1 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.other _ (by decide), u2.other _ (by decide),
      o1 _ (by decide)]
  obtain e4 : s6.gpr .r4 = σ.gpr .r2 := by
    rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      o1 _ (by decide)]
  obtain e6 : s6.gpr .r6 = σ.gpr .r3 := by
    rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      o1 _ (by decide)]
  -- `setup`.
  unfold setup ctxK
  simp only [List.append_assoc, List.cons_append]
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s8 u8 => ?_
  obtain h9 : s8.gpr .r9 = BitVec.ofNat 32 (geo iS σ).w := by
    rw [u8.gpr, u7.gpr, dpVal, e11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (3 : BitVec 32).toNat = 3 from rfl]
    simp only [Geo.w, fK] at *
    omega_arith
  refine stride_ok (by omega_arith) h9 fun s9 h7 r9 m9 => ?_
  obtain r79 : Rest [.r9, .r7] s6 s9 := (u7.rest (by simp)).trans ((u8.rest (by simp)).trans (r9.mono (by simp)))
  obtain m79 : s9.mem = s6.mem := m9.trans (u8.mem.trans u7.mem)
  obtain ws9 : Ws s9 (geo iS σ).B (geo iS σ).Z (geo iS σ).w nArr :=
    ⟨fS, by rw [r79.wr, r6'.wr, b1.wr, h.wr]; simp, fits, by omega_arith, by omega_arith, h7,
      by rw [r79.gpr _ (by decide), e8], by rw [r9.gpr _ (by decide), h9]⟩
  obtain b9 := b6.of_rest r79 m79
  refine wp_strSlot ws9 (d := 16) (by decide) fun s10 u10 => ?_
  obtain ws10 := ws9.of_mupd u10
  obtain hz : 64 ≤ (geo iS σ).Z := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega_arith) fits
  obtain o10 := writeW32_outside s9.mem (State.addr (geo iS σ).B) (d := 16) (s9.gpr .r9) (by decide)
  rw [← u10.mem] at o10
  obtain b10 := b9.outside o10 (by omega_arith) (by omega_arith) u10.sp u10.rd u10.wr
  obtain c10 : s10.mem.readW (off (State.addr (geo iS σ).B) 16) 32 = BitVec.ofNat 32 (geo iS σ).w := by
    rw [u10.mem, Mem.readW_writeW_self32, ws9.r9]
  refine wp_dp (op2_imm (by decide)) fun s11 u11 => ?_
  refine wp_mov (op2_imm (by decide)) fun s12 u12 => ?_
  refine wp_mul fun s13 u13 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s14 u14 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u15 => WP.block_nil ?_
  obtain rest : Rest [.r0, .lr, .r3] s10 u := (u11.rest (by simp)).trans ((u12.rest (by simp)).trans
    ((u13.rest (by simp)).trans ((u14.rest (by simp)).trans (u15.rest (by simp)))))
  obtain mu : u.mem = s10.mem := by rw [u15.mem, u14.mem, u13.mem, u12.mem, u11.mem]
  obtain bu := b10.of_rest rest mu
  obtain hu := ws10.rest rest
  obtain p0 : u.gpr .r0 = (geo iS σ).B + BitVec.ofNat 32 hdr := by
    rw [u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide), u11.gpr,
      dpVal, ws10.r8]
  obtain plr : u.gpr .lr = BitVec.ofNat 32 (nArr * ((geo iS σ).w + 2)) := by
    rw [u15.other _ (by decide), u14.gpr, u13.gpr, u12.gpr, u12.other _ (by decide), u11.other _ (by decide),
      ws10.r7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nArr, S]
    rw [Nat.mod_eq_of_lt (a := 24) (by decide), Nat.mod_eq_of_lt (a := 4 * ((geo iS σ).w + 2)) (by omega_arith),
      Nat.mod_eq_of_lt (a := 24 * (4 * ((geo iS σ).w + 2))) (by omega_arith),
      Nat.mod_eq_of_lt (a := 24 * ((geo iS σ).w + 2)) (by omega_arith)]
    omega_arith
  obtain nfit : hdr + 4 * (nArr * ((geo iS σ).w + 2)) ≤ (geo iS σ).Z := by
    simp only [arr, S, nArr] at fits ⊢; omega_arith
  refine WP.mono (zero_ok u (base := (geo iS σ).B) (size := (geo iS σ).Z) (o := hdr) (n := nArr * ((geo iS σ).w + 2))
    ⟨fS, nfit, ⟨rS iS σ, by rw [bu.wr, h.wr]; simp, Region.contains_self _ _⟩⟩
    (by simp only [nArr]; omega_arith) p0 plr (by rw [u15.gpr])) fun t inv => ?_
  obtain bt := bu.outside inv.outside (by simp only [hdr]; omega_arith) nfit inv.rest.sp inv.rest.rd inv.rest.wr
  obtain rT : Rest [.r0, .lr, .r3, .r7, .r9] s6 t :=
    (r79.mono (by simp)).trans ((u10.rest _).trans ((rest.trans (inv.rest.mono (by simp))).mono (by simp)))
  refine ⟨⟨bt, hu.rest inv.rest, ?_, fun j hj => ?_, by rw [rT.gpr _ (by decide), e10],
    by rw [rT.gpr _ (by decide), e11]⟩, by rw [rT.gpr _ (by decide), e4], by rw [rT.gpr _ (by decide), e6]⟩
  · have e := inv.outside.w32 (d := 16) (by simp only [hdr]; omega_arith) (by omega_arith)
    apply BitVec.eq_of_toNat_eq
    rw [show (t.mem.readW (off (State.addr (geo iS σ).B) 16) 32).toNat = w32 t.mem (State.addr (geo iS σ).B) 16
      from rfl, e, show w32 u.mem (State.addr (geo iS σ).B) 16 = (u.mem.readW (off (State.addr (geo iS σ).B) 16) 32).toNat
      from rfl, mu, c10]
  · have := VG.Proof.Rsa.Arm.CrtValues.val32_zero_part inv.value (a := j * ((geo iS σ).w + 2))
      (c := (geo iS σ).w + 2) (by
      have := Nat.mul_le_mul_right ((geo iS σ).w + 2) (show j + 1 ≤ nArr by omega_arith)
      rw [Nat.succ_mul] at this; omega_arith)
    simpa only [arr, S, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

end

end VG.Proof.Rsa.Arm.KeyCheck

end

end


/-! # The checks of an RSA key on ARMv7: the numbers read into arrays

`EntSt.load_ok`: `load j` reads a number into array `j`; `loads_ok`: the
numbers on the stack, by induction over the list of them.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.CrtValues (reg val32_off Keep.of_frame_arr bytes_frame)

section
variable {nA iS : Nat} {ins : List (Nat × Nat)}

/-- The number at `src`, `k` bytes long. -/
abbrev bytesV (σ : State) (src : BitVec 32) (k : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr src) k)

theorem EntSt.of_rest {σ s t : State} {A : Nat → Nat} (h : EntSt nA iS ins σ s A) {ws : List Reg}
    (r : Rest ws s t) (m : t.mem = s.mem) (h10 : Reg.r10 ∉ ws) (h11 : Reg.r11 ∉ ws) (h7 : Reg.r7 ∉ ws)
    (h8 : Reg.r8 ∉ ws) (h9 : Reg.r9 ∉ ws) : EntSt nA iS ins σ t A :=
  ⟨h.base.of_rest r m, h.ws.rest r h7 h8 h9, m ▸ h.cnt, fun j hj => m ▸ h.full j hj,
    (r.gpr _ h10).trans h.r10, (r.gpr _ h11).trans h.r11⟩

/-- `load j`: array `j` := the `k` bytes at `r4` (`r6 = k`). -/
theorem EntSt.load_ok {σ s : State} {A : Nat → Nat} (h : EntSt nA iS ins σ s A) {j : Nat} (hj : j < nArr)
    {src : BitVec 32} {k : Nat} (hrd : reg src k ∈ σ.rd) (hsep : (reg src k).Disjoint (rS iS σ))
    (fit : src.toNat + k ≤ 2 ^ 32) (pos : 0 < k) (le : k ≤ fK σ)
    (p4 : s.gpr .r4 = src) (p6 : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (CrtValues.load j) s fun t => EntSt nA iS ins σ t (upd A j (bytesV σ src k)) ∧
      Rest [.r0, .r1, .r2, .r3, .r5, .lr] s t := by
  have pre := h.base.pre
  have hw := h.ws
  obtain fit' := hw.arr_fit hj
  have nw := hw.nowrap
  have w16 := pre.w16
  have kb := pre.kb
  have hS : S (geo iS σ).w = 4 * ((geo iS σ).w + 2) := rfl
  obtain hkw : k ≤ 4 * (geo iS σ).w := by
    have : (geo iS σ).w = (fK σ + 3) / 4 := rfl
    omega_arith
  obtain hB : (geo iS σ).B.toNat + (arr (geo iS σ).w j + 4 * ((geo iS σ).w + 2)) ≤ 2 ^ 32 := by
    obtain f2 : arr (geo iS σ).w j + 4 * ((geo iS σ).w + 2) ≤ (geo iS σ).Z := hw.arr_fit hj
    have := hw.nowrap
    omega_arith
  rw [CrtValues.load, WP.seq_iff]
  refine ptr_ok hw (by decide) (by simp only [nArr] at hj; omega_arith) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u4 => WP.block_nil ?_
  obtain rest : Rest [.r0, .r3, .r5, .lr] s u :=
    (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  obtain mu : u.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, m1]
  obtain bu := h.base.of_rest rest mu
  obtain hu := hw.rest rest
  obtain ad : State.addr ((geo iS σ).B + BitVec.ofNat 32 (arr (geo iS σ).w j)) =
      off (State.addr (geo iS σ).B) (arr (geo iS σ).w j) := hw.addr (by omega_arith)
  obtain p0 : u.gpr .r0 = (geo iS σ).B + BitVec.ofNat 32 (arr (geo iS σ).w j) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p1]
  refine WP.mono (loadBE_ok u (src := src) (dst := (geo iS σ).B + BitVec.ofNat 32 (arr (geo iS σ).w j))
    (n := (geo iS σ).w + 2) pos (by omega_arith) (by omega_arith) fit
    (by rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith)
    ⟨reg src k, List.mem_append_left _ (by rw [bu.rd]; exact hrd), Region.contains_self _ _⟩
    ⟨rS iS σ, by rw [bu.wr, pre.wr]; simp, by rw [ad]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    (by rw [ad]
        refine fun a ha hb => hsep a ha ?_
        exact Region.Contains.byte (r := rS iS σ) (b := off (State.addr (geo iS σ).B) (arr (geo iS σ).w j))
          (n := 4 * ((geo iS σ).w + 2)) (Offset.contains_base _ (by omega_arith) (by omega_arith))
          (by simp only [Region.Contains] at hb ⊢; omega_arith))
    p0 (by rw [rest.gpr _ (by decide), p4])
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, p1])
    (by rw [rest.gpr _ (by decide), p6])
    (by rw [u4.other _ (by decide), u3.gpr, dpVal, u2.other .r9 (by decide), r1.gpr .r9 (by decide), hw.r9,
          BitVec.ofNat_add]; rfl)
    (by rw [u4.gpr])) ?_
  rintro t ⟨v, f, r⟩
  rw [ad] at f v
  obtain k' : Keep (geo iS σ).B (geo iS σ).w [j] [] u.mem t.mem := Keep.of_frame_arr f (by omega_arith)
  obtain RT : Rest [.r0, .r1, .r2, .r3, .r5, .lr] s t := (rest.mono (by simp)).trans (r.mono (by simp))
  refine ⟨⟨bu.keep k' (by simpa using hj) (by simp) (by simp) r.sp r.rd r.wr, hu.rest r, ?_, fun i hi => ?_,
    (RT.gpr _ (by decide)).trans h.r10, (RT.gpr _ (by decide)).trans h.r11⟩, RT⟩
  · rw [slot_eq_of_keep k' (by decide) (by simp), mu, h.cnt]
  · simp only [upd]
    split
    · subst i
      rw [val32_off, Nat.add_zero] at v
      rw [v, mu, bytes_frame h.base.frame (by simpa using hsep) (by omega_arith)]
    · rename_i hne
      rw [k'.full (by simpa using fun e => hne e.symm) (by simp) (hw.fit64 hi), mu, h.full i hi]

/-- The `i`-th input on the stack. -/
abbrev inV (σ : State) (i : Nat) : Nat := bytesV σ (stackArg σ i) (stackArg σ (i + 1)).toNat

/-- `loadArg (4 i) j`: array `j` := the input at stack word `i`. -/
theorem EntSt.loadArg_ok {σ s : State} {A : Nat → Nat} (h : EntSt nA iS ins σ s A) {p : Nat × Nat}
    (hp : p ∈ ins) {rest : List (Prog isa)} (hr : rest ≠ []) {Q : State → Prop}
    (k : ∀ t, EntSt nA iS ins σ t (upd A p.2 (inV σ p.1)) → WP isa (seqs rest) t Q) :
    WP isa (seqs (loadArg (4 * p.1) p.2 ++ rest)) s Q := by
  have pre := h.base.pre
  have hA := pre.hA
  obtain hi := pre.hIns p hp
  obtain hn := pre.ins1 p hp
  unfold loadArg CrtValues.args
  rw [List.cons_append, List.cons_append, List.nil_append, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine h.base.ldrSp (i := p.1) (by omega_arith) (by omega_arith) fun s1 b1 u1 => ?_
  obtain e : 4 * p.1 + 4 = 4 * (p.1 + 1) := by omega_arith
  rw [e]
  refine b1.ldrSp (i := p.1 + 1) hi.1 (by omega_arith) fun s2 b2 u2 => WP.block_nil ?_
  obtain h2 : EntSt nA iS ins σ s2 A :=
    (h.of_rest ((u1.rest (ws := [.r4, .r6]) (by simp)).trans (u2.rest (ws := [.r4, .r6]) (by simp)))
      (u2.mem.trans u1.mem) (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [wp_seqs_cons hr]
  refine WP.mono (h2.load_ok hi.2.1 (src := stackArg σ p.1) (k := (stackArg σ (p.1 + 1)).toNat)
    (pre.rdIns p hp) (pre.insS p hp) (pre.fIns p hp) hn.1 hn.2
    (by rw [u2.other _ (by decide), u1.gpr]) (by rw [u2.gpr]; simp)) fun t ⟨ht, _⟩ => k t ht

/-- What the loads of `l` leave, from `A`. -/
def loadFn (σ : State) : List (Nat × Nat) → (Nat → Nat) → Nat → Nat
  | [], A => A
  | p :: l, A => loadFn σ l (upd A p.2 (inV σ p.1))

theorem EntSt.loads_ok {σ s : State} {A : Nat → Nat} (h : EntSt nA iS ins σ s A) (l : List (Nat × Nat))
    (hl : ∀ p ∈ l, p ∈ ins) {rest : List (Prog isa)} (hr : rest ≠ []) {Q : State → Prop}
    (k : ∀ t, EntSt nA iS ins σ t (loadFn σ l A) → WP isa (seqs rest) t Q) :
    WP isa (seqs ((l.map fun p => (4 * p.1, p.2)).flatMap (fun a => loadArg a.1 a.2) ++ rest)) s Q := by
  induction l generalizing s A with
  | nil => exact k s h
  | cons p l ih =>
    rw [List.map_cons, List.flatMap_cons, List.append_assoc]
    exact h.loadArg_ok (hl p List.mem_cons_self) (by simp [hr]) fun t ht =>
      ih ht (fun q hq => hl q (List.mem_cons_of_mem _ hq)) k

end

end VG.Proof.Rsa.Arm.KeyCheck

end

end

/-! # The checks of an RSA key on ARMv7: the entry, the checks of `n` and `e`, and the exit

`entry_ok`: the entry reads the numbers and checks `n` (`Mid`, and Z);
`eCheck_ok`: `e` checked (Z); `Mid.bodyIn`: what the checks start from;
`ret_ok`, `restore_ok`: the mask returned and the registers restored.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.CrtValues (reg bytes_frame num_of_full num_of_zero top_of_full val32_low2)

section
variable {nA iS : Nat} {ins : List (Nat × Nat)}

/-- `n` and `e`. -/
abbrev nV (σ : State) : Nat := bytesV σ (σ.gpr .r0) (fK σ)
abbrev eV (σ : State) : Nat := bytesV σ (σ.gpr .r2) (σ.gpr .r3).toNat

/-- The arrays after the entry. -/
def aEnt (ins : List (Nat × Nat)) (σ : State) : Nat → Nat :=
  upd (loadFn σ ins (upd (fun _ => 0) aE (eV σ))) aN (nV σ)

/-- After the entry, and the check of `e`. -/
structure Mid (nA iS : Nat) (ins : List (Nat × Nat)) (σ s : State) (A : Nat → Nat) : Prop where
  base : FnBase nA iS ins σ s
  ws : WsR s (geo iS σ).B (geo iS σ).Z (geo iS σ).w nArr
  cnt : s.mem.readW (off (State.addr (geo iS σ).B) 16) 32 = BitVec.ofNat 32 (geo iS σ).w
  full : ∀ j < nArr, val32 s.mem (State.addr (geo iS σ).B) (arr (geo iS σ).w j) ((geo iS σ).w + 2) = A j
  r11 : s.gpr .r11 = σ.gpr .r1

theorem Mid.of_rest {σ s t : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A) {ws : List Reg} (r : Rest ws s t)
    (m : t.mem = s.mem) (h8 : Reg.r8 ∉ ws) (h11 : Reg.r11 ∉ ws) : Mid nA iS ins σ t A :=
  ⟨h.base.of_rest r m, ⟨h.ws.nowrap, by rw [r.wr]; exact h.ws.writable, h.ws.fits, h.ws.wpos, h.ws.wle,
    (r.gpr _ h8).trans h.ws.r8⟩, m ▸ h.cnt, fun j hj => m ▸ h.full j hj, (r.gpr _ h11).trans h.r11⟩

theorem EntSt.mid {σ s : State} {A : Nat → Nat} (h : EntSt nA iS ins σ s A) : Mid nA iS ins σ s A :=
  ⟨h.base, Ws.toR h.ws, h.cnt, h.full, h.r11⟩

theorem entry_ok {σ : State} (h : FnPre nA iS ins σ) (h4 : 4 * iS < 4096) :
    WP isa (entry (4 * iS) (ins.map fun p => (4 * p.1, p.2))) σ fun t =>
      Mid nA iS ins σ t (aEnt ins σ) ∧ t.z = Spec.Rsa.modulusValid (nV σ) (fK σ) := by
  have kb := h.kb
  unfold entry
  rw [show ∀ (a b c : Prog isa) (l m : List (Prog isa)), [a, b, c] ++ l ++ m = [a, b] ++ (c :: (l ++ m)) from
    fun _ _ _ _ _ => by simp, wp_seqs_append (by simp) (by simp)]
  refine WP.mono (entryFirst_ok h h4) fun t1 ⟨e1, p4, p6⟩ => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (e1.load_ok (j := aE) (by decide) (src := σ.gpr .r2) (k := (σ.gpr .r3).toNat) h.rdE h.eS h.fE
    (by have := h.e1; omega_arith) h.e2 p4 (by rw [p6]; simp)) fun t2 ⟨e2, _⟩ => ?_
  refine e2.loads_ok ins (fun p hp => hp) (by simp) fun t3 e3 => ?_
  rw [wp_seqs_cons (by simp)]
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun s5 u5 => WP.block_nil ?_
  obtain e5 := e3.of_rest ((u4.rest (ws := [.r4, .r6]) (by simp)).trans (u5.rest (by simp))) (u5.mem.trans u4.mem)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (e5.load_ok (j := aN) (by decide) (src := σ.gpr .r0) (k := fK σ) h.rdN h.nS h.fN
    (by omega_arith) (Nat.le_refl _) (by rw [u5.other _ (by decide), u4.gpr, e3.r10])
    (by rw [u5.gpr, u4.other _ (by decide), e3.r11]; simp)) fun t6 ⟨e6, r6⟩ => ?_
  obtain p4' : t6.gpr .r4 = σ.gpr .r0 := by
    rw [r6.gpr _ (by decide), u5.other _ (by decide), u4.gpr, e3.r10]
  obtain p6' : t6.gpr .r6 = BitVec.ofNat 32 (fK σ) := by
    rw [r6.gpr _ (by decide), u5.gpr, u4.other _ (by decide), e3.r11]; simp
  refine WP.mono (modulusCheck_ok t6 (src := σ.gpr .r0) (k := fK σ) kb.1 kb.2 h.fN
    ⟨_, List.mem_append_left _ (by rw [e6.base.rd]; exact h.rdN), Region.contains_self _ _⟩ p4' p6')
    fun t ⟨z, m, r⟩ => ⟨e6.mid.of_rest r m (by decide) (by decide), ?_⟩
  rw [z, bytes_frame e6.base.frame (by simpa using h.nS) (by omega_arith)]

/-- The bytes of `e`. -/
abbrev eBytes (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr (σ.gpr .r2)) (σ.gpr .r3).toNat

/-- `e` and `e_len` into `r1` and `lr`, for `exponentCheck`. -/
theorem eLoad_ok {σ s : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A) :
    WP isa (.block [.ldr .r1 .r8 sE, .ldr .lr .r8 sEl]) s fun t => Mid nA iS ins σ t A ∧
      ExponentInput (σ.gpr .r2) (eBytes σ) t := by
  have pre := h.base.pre
  have fits := pre.fits
  have nw := h.ws.nowrap
  have eZ : (geo iS σ).Z = (stackArg σ (iS + 1)).toNat * 8 := rfl
  have eB : (geo iS σ).B.toNat = (stackArg σ iS).toNat := rfl
  have fS := pre.fS
  obtain hz : 64 ≤ (geo iS σ).Z := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega_arith) fits
  obtain rdS : (geo iS σ).B.toNat + 64 ≤ 2 ^ 32 := by omega_arith
  obtain ldS : ∀ (d : Nat) (u : State), Mid nA iS ins σ u A → d + 4 ≤ 64 →
      State.addr (u.gpr .r8 + BitVec.ofNat 32 d) = off (State.addr (geo iS σ).B) d ∧
      InRegions (u.rd ++ u.wr) (off (State.addr (geo iS σ).B) d) 4 := fun d u hu hd =>
    ⟨by rw [hu.ws.r8]; exact VG.Arm.addr_add (by omega_arith),
      ⟨rS iS σ, List.mem_append_right _ (by rw [hu.base.wr, pre.wr]; simp),
        Offset.contains_base _ (by omega_arith) (by omega_arith)⟩⟩
  refine wp_ldr (by decide) (ldS sE s h (by decide)).1 (ldS sE s h (by decide)).2 fun s1 u1 => ?_
  obtain h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem (by decide) (by decide)
  refine wp_ldr (by decide) (ldS sEl s1 h1 (by decide)).1 (ldS sEl s1 h1 (by decide)).2
    fun s2 u2 => WP.block_nil ?_
  obtain h2 := h1.of_rest (u2.rest (ws := [.lr]) (by simp)) u2.mem (by decide) (by decide)
  obtain e1 : s2.gpr .r1 = σ.gpr .r2 := by
    rw [u2.other _ (by decide), u1.gpr]
    exact BitVec.eq_of_toNat_eq (h.base.saved 9 (by decide))
  obtain e2 : s2.gpr .lr = σ.gpr .r3 := by
    rw [u2.gpr, u1.mem]
    exact BitVec.eq_of_toNat_eq (h.base.saved 10 (by decide))
  have le := pre.e2
  have kb := pre.kb
  obtain len : (eBytes σ).length = (σ.gpr .r3).toNat := VG.Proof.Rsa.Arm.CrtValues.bytesAt_length _ _ _
  refine ⟨h2, ⟨by rw [len]; omega_arith, by rw [len]; exact pre.fE,
    by rw [len]; exact ⟨_, List.mem_append_left _ (by rw [h2.base.rd]; exact pre.rdE), Region.contains_self _ _⟩,
    fun i hi => ?_⟩, e1, by rw [len, e2]; simp⟩
  rw [len] at hi
  have := bytes_frame h2.base.frame (a := State.addr (σ.gpr .r2)) (n := (σ.gpr .r3).toNat)
    (by simpa using pre.eS) (by omega_arith)
  simp only [Spec.Rsa.bytesAt] at this ⊢
  have := congrArg (fun l => l[i]?) this
  simpa [hi] using this

/-- `exponentCheck`, from its input. -/
theorem expCheck_ok {σ s : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A)
    (hi : ExponentInput (σ.gpr .r2) (eBytes σ) s) :
    WP isa exponentCheck s fun t => Mid nA iS ins σ t A ∧
      t.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (eV σ)).toNat := by
  have pre := h.base.pre
  obtain len : (eBytes σ).length = (σ.gpr .r3).toNat := VG.Proof.Rsa.Arm.CrtValues.bytesAt_length _ _ _
  exact WP.mono (exponentCheck_ok s (by rw [len]; exact pre.e1) hi.1.countFit hi.1.sourceFit hi.1.read
    hi.1.bytes hi.2.1 hi.2.2) fun t ⟨v, m, r⟩ => ⟨h.of_rest r m (by decide) (by decide), v⟩

/-- `cmp r7, #1`. -/
theorem eCmp_ok {σ s : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (eV σ)).toNat) :
    WP isa (.block [.cmp .r7 (.imm 1)]) s fun t => Mid nA iS ins σ t A ∧
      t.z = Spec.Rsa.exponentValid (eV σ) :=
  wp_cmp (op2_imm (by decide)) fun t u4 z4 => WP.block_nil ⟨h.of_rest (u4.rest []) u4.mem
    (by simp) (by simp), by rw [z4, h7]; cases Spec.Rsa.exponentValid (eV σ) <;> rfl⟩

/-- `eCheck`: Z if `e` is valid. -/
theorem eCheck_ok {σ s : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A) :
    WP isa eCheck s fun t => Mid nA iS ins σ t A ∧ t.z = Spec.Rsa.exponentValid (eV σ) := by
  unfold eCheck
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eLoad_ok h) fun s1 ⟨h1, i1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  exact WP.mono (expCheck_ok h1 i1) fun s2 ⟨h2, v2⟩ => eCmp_ok h2 v2

/-- What the checks start from. -/
theorem Mid.bodyIn {σ s : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A) (v : Vals)
    (hv : A = vals v) (hA : ∀ j < nArr, A j < 2 ^ (32 * (geo iS σ).w)) : BodyIn (geo iS σ) v s := by
  have pre := h.base.pre
  have w16 := pre.w16
  obtain hvj : ∀ j < nArr, A j = vals v j := fun j _ => by rw [hv]
  refine ⟨h.ws.nowrap, h.ws.writable, h.ws.fits, pre.kb, h.ws.r8, by rw [h.r11]; simp, h.cnt, fun j hj => ?_,
    ?_⟩
  · have hj' := List.mem_range.mp hj
    rw [← hvj j hj', ← h.full j hj']
    exact val32_low2 (by rw [h.full j hj']; exact hA j hj')
  · have := h.full aVD (by decide)
    obtain hz : A aVD = 0 := by rw [hvj _ (by decide)]; rfl
    exact top_of_full (this.trans hz)

/-- `ret`: the mask returned. -/
theorem ret_ok {σ s : State} {c : Bool} (h : FnBase nA iS ins σ s) (h8 : s.gpr .r8 = (geo iS σ).B)
    (hm : slot s.mem (geo iS σ).B sMask = if c then 1 else 0) :
    WP isa (.block ret) s fun t => FnBase nA iS ins σ t ∧ t.gpr .r0 = BitVec.ofNat 32 (if c then 1 else 0) := by
  have pre := h.pre
  have fits := pre.fits
  have fS := pre.fS
  obtain hz : 160 ≤ (geo iS σ).Z := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega_arith) fits
  have eZ : (geo iS σ).Z = (stackArg σ (iS + 1)).toNat * 8 := rfl
  have eB : (geo iS σ).B.toNat = (stackArg σ iS).toNat := rfl
  have eM : sMask = 120 := rfl
  refine wp_ldr (by decide) (by rw [h8]; exact VG.Arm.addr_add (by omega_arith))
    ⟨rS iS σ, List.mem_append_right _ (by rw [h.wr, pre.wr]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    fun t u => WP.block_nil ⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, ?_⟩
  rw [u.gpr]
  apply BitVec.eq_of_toNat_eq
  rw [show (s.mem.readW (off (State.addr (geo iS σ).B) sMask) 32).toNat = slot s.mem (geo iS σ).B sMask from rfl,
    hm]
  cases c <;> rfl

theorem ldrSaved {σ s : State} (h : FnBase nA iS ins σ s) (p12 : s.gpr .r12 = (geo iS σ).B) {i : Nat}
    (hi : i < 11) {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (σ.gpr (savedReg i)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldr t .r12 (20 + 4 * i) :: rest)) s Q := by
  have pre := h.pre
  have fS := pre.fS
  have fits := pre.fits
  obtain hz : 64 ≤ (geo iS σ).Z := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega_arith) fits
  have eZ : (geo iS σ).Z = (stackArg σ (iS + 1)).toNat * 8 := rfl
  have eB : (geo iS σ).B.toNat = (stackArg σ iS).toNat := rfl
  refine wp_ldr (by omega_arith) (by rw [p12]; exact addr_add (by omega_arith))
    ⟨rS iS σ, List.mem_append_right _ (by rw [h.wr, pre.wr]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    fun s' u => k s' ?_
  obtain e : s.mem.readW (off (State.addr (geo iS σ).B) (20 + 4 * i)) 32 = σ.gpr (savedReg i) :=
    BitVec.eq_of_toNat_eq (h.saved i hi)
  exact ⟨by rw [u.gpr]; exact e, u.other, u.mem, u.rd, u.wr, u.sp⟩

theorem restore_ok {σ s : State} (h : FnBase nA iS ins σ s) (h4 : 4 * iS < 4096) :
    WP isa (.block (restore (4 * iS))) s fun t => (∀ r ∈ preserved, t.gpr r = σ.gpr r) ∧ t.sp = σ.sp ∧
      t.mem = s.mem ∧ t.gpr .r0 = s.gpr .r0 := by
  have pre := h.pre
  refine h.ldrSp (i := iS) (by have := pre.hS; omega_arith) h4 fun s1 d1 u1 => ?_
  have p12 : s1.gpr .r12 = (geo iS σ).B := u1.gpr
  refine ldrSaved d1 p12 (i := 0) (by decide) fun s2 u2 => ?_
  obtain d2 := d1.of_rest (u2.rest (ws := [.r4]) (by simp)) u2.mem
  refine ldrSaved d2 (by rw [u2.other _ (by decide), p12]) (i := 1) (by decide) fun s3 u3 => ?_
  obtain d3 := d2.of_rest (u3.rest (ws := [.r5]) (by simp)) u3.mem
  refine ldrSaved d3 (by rw [u3.other _ (by decide), u2.other _ (by decide), p12]) (i := 2) (by decide)
    fun s4 u4 => ?_
  obtain d4 := d3.of_rest (u4.rest (ws := [.r6]) (by simp)) u4.mem
  obtain q4 : s4.gpr .r12 = (geo iS σ).B := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p12]
  refine ldrSaved d4 q4 (i := 3) (by decide) fun s5 u5 => ?_
  obtain d5 := d4.of_rest (u5.rest (ws := [.r7]) (by simp)) u5.mem
  refine ldrSaved d5 (by rw [u5.other _ (by decide), q4]) (i := 4) (by decide) fun s6 u6 => ?_
  obtain d6 := d5.of_rest (u6.rest (ws := [.r8]) (by simp)) u6.mem
  obtain q6 : s6.gpr .r12 = (geo iS σ).B := by rw [u6.other _ (by decide), u5.other _ (by decide), q4]
  refine ldrSaved d6 q6 (i := 5) (by decide) fun s7 u7 => ?_
  obtain d7 := d6.of_rest (u7.rest (ws := [.r9]) (by simp)) u7.mem
  refine ldrSaved d7 (by rw [u7.other _ (by decide), q6]) (i := 6) (by decide) fun s8 u8 => ?_
  obtain d8 := d7.of_rest (u8.rest (ws := [.r10]) (by simp)) u8.mem
  obtain q8 : s8.gpr .r12 = (geo iS σ).B := by rw [u8.other _ (by decide), u7.other _ (by decide), q6]
  refine ldrSaved d8 q8 (i := 7) (by decide) fun s9 u9 => ?_
  obtain d9 := d8.of_rest (u9.rest (ws := [.r11]) (by simp)) u9.mem
  refine ldrSaved d9 (by rw [u9.other _ (by decide), q8]) (i := 8) (by decide) fun t u10 => WP.block_nil ?_
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.gpr]; rfl
    · rw [u10.other _ (by decide), u9.gpr]; rfl
    · rw [u10.gpr]; rfl
  · rw [u10.sp, d9.sp]
  · rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide)]

/-- The function's result, from the checks' mask `c` (with `P c`). -/
def FnPost (σ u : State) (P : Bool → Prop) : Prop :=
  abiPreserved σ u ∧ ∃ c : Bool,
    (Spec.Rsa.modulusValid (nV σ) (fK σ) = true → Spec.Rsa.exponentValid (eV σ) = true → P c) ∧
    u.gpr .r0 = BitVec.ofNat 32
      (if Spec.Rsa.modulusValid (nV σ) (fK σ) && Spec.Rsa.exponentValid (eV σ) && c then 1 else 0)

/-- A function: the entry, the checks `body`, the exit. -/
theorem fn_ok {σ : State} (h : FnPre nA iS ins σ) (h4 : 4 * iS < 4096) {body : Prog isa} {v : Vals}
    {P : Bool → Prop} (hv : aEnt ins σ = vals v)
    (hA : ∀ j < nArr, aEnt ins σ j < 2 ^ (32 * (geo iS σ).w))
    (hbody : ∀ s, Mid nA iS ins σ s (aEnt ins σ) → BodyIn (geo iS σ) v s →
      Spec.Rsa.modulusValid (nV σ) (fK σ) = true → Spec.Rsa.exponentValid (eV σ) = true →
      WP isa body s fun t => ∃ A live c, Stg (geo iS σ) s A live c t ∧ P c) :
    WP isa (fn (4 * iS) (ins.map fun p => (4 * p.1, p.2)) body) σ fun u => FnPost σ u P := by
  unfold fn
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (entry_ok h h4) fun s1 ⟨m1, z1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  -- What the three ways out leave for `restore`.
  obtain exit : ∀ (u : State) (c : Bool), FnBase nA iS ins σ u → (Spec.Rsa.modulusValid (nV σ) (fK σ) = true →
      Spec.Rsa.exponentValid (eV σ) = true → P c) →
      u.gpr .r0 = BitVec.ofNat 32
        (if Spec.Rsa.modulusValid (nV σ) (fK σ) && Spec.Rsa.exponentValid (eV σ) && c then 1 else 0) →
      WP isa (seqs [.block (restore (4 * iS))]) u fun u' => FnPost σ u' P := fun u c hu hp hr =>
    WP.mono (restore_ok hu h4) fun u' ⟨pres, sp, _, r0⟩ => ⟨⟨pres, sp⟩, c, hp, r0.trans hr⟩
  refine WP.ite s1.z rfl (fun hn => ?_) (fun hn => ?_)
  · rw [WP.seq_iff]
    refine WP.mono (eCheck_ok m1) fun s2 ⟨m2, z2⟩ => ?_
    refine WP.ite s2.z rfl (fun he => ?_) (fun he => ?_)
    · rw [WP.seq_iff]
      obtain bi := m2.bodyIn v hv hA
      refine WP.mono (hbody s2 m2 bi (by rw [← z1]; exact hn) (by rw [← z2]; exact he)) fun t ⟨A, live, c, ht, hP⟩ => ?_
      obtain bt : FnBase nA iS ins σ t := m2.base.keep ht.keep (fun j hj => List.mem_range.mp hj) (by decide)
        (by decide) ht.rest.sp ht.rest.rd ht.rest.wr
      refine WP.mono (ret_ok bt ht.ws.r8 ht.mask) fun u ⟨bu, ru⟩ => exit u c bu (fun _ _ => hP) ?_
      rw [ru, ← z1, ← z2, hn, he]
      rfl
    · refine wp_mov (op2_imm (by decide)) fun u up => WP.block_nil ?_
      refine exit u false (m2.base.of_rest (up.rest (ws := [.r0]) (by simp)) up.mem) (fun _ e => ?_) ?_
      · rw [← z2, he] at e; cases e
      · rw [up.gpr, ← z2, he]; simp
  · refine wp_mov (op2_imm (by decide)) fun u up => WP.block_nil ?_
    refine exit u false (m1.base.of_rest (up.rest (ws := [.r0]) (by simp)) up.mem) (fun e _ => ?_) ?_
    · rw [← z1, hn] at e; cases e
    · rw [up.gpr, ← z1, hn]; simp

end

end VG.Proof.Rsa.Arm.KeyCheck

end

end

/-! ### `Rsa.Arm.KcCT`, which this module and modules that import it used -/

section

/-! ### `Rsa.Arm.KcBody`, which this module and modules that import it used -/

section

/-! # The checks of an RSA key on ARMv7: `crtBody` and `keyBody`

`crtBody_ok`: from `BodyIn`, the mask is `crtBits` of what the code computes
(`CrtOut`); `keyBody_ok`: then and'ed with `d < n` and the remainders of `d`
modulo `p - 1` and `q - 1` equal to `dP` and `dQ` (`KeyOut`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- What the products are, when their factors are below their moduli. -/
def ProdsOk (g : Geo) (v : Vals) (R₁ R₂ R₃ : Nat) : Prop :=
  (v.dP < 2 * (v.p / 2) → 2 * (2 * (v.p / 2)) ≤ 2 ^ (32 * g.w) →
    R₁ = v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2))) ∧
  (v.dQ < 2 * (v.q / 2) → 2 * (2 * (v.q / 2)) ≤ 2 ^ (32 * g.w) →
    R₂ = v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2))) ∧
  (v.qI < v.p → 2 * v.p ≤ 2 ^ (32 * g.w) → R₃ = v.q % 2 ^ (32 * g.w) * v.qI % v.p)

/-- After the division of `n` by `p`. -/
def DivN (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ X₁ X₂,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧
  StgD g s0 (aDivN v X₁ X₂) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) t

/-- `ctxDiv` after it. -/
def DivN' (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ X₁ X₂,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧
  Stg g s0 (aDivN v X₁ X₂) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) t

/-- After `crtBody`. -/
def CrtOut (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ X₁ X₂ R₁ R₂ R₃,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧ ProdsOk g v R₁ R₂ R₃ ∧
  Stg g s0 (aFin v) liveFin (VG.Proof.Rsa.crtBits v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃) t

theorem divN_ctx_ok {g : Geo} {s0 s : State} {v : Vals} (h : DivN g s0 v s) :
    WP isa (.block ctxDiv) s (DivN' g s0 v) := by
  obtain ⟨X₁, X₂, hX, h⟩ := h
  exact WP.mono h.ctx_ok fun t ht => ⟨X₁, X₂, hX, ht⟩

theorem crtChecks_ok' {g : Geo} {s0 s : State} {v : Vals} (h : DivN' g s0 v s) :
    WP isa crtChecks s (CrtOut g s0 v) := by
  obtain ⟨X₁, X₂, hX, h⟩ := h
  exact WP.mono (crtChecks_ok h) fun t ⟨R₁, R₂, R₃, h1, h2, h3, ht⟩ => ⟨X₁, X₂, R₁, R₂, R₃, hX, ⟨h1, h2, h3⟩, ht⟩

theorem start_ok' {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa start s fun u => VG.Proof.Rsa.Arm.Div.Context (gDiv g) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (DivN g s v) :=
  WP.mono (start_ok h) fun _ ⟨c, w⟩ => ⟨c, WP.mono w fun _ ⟨X₁, X₂, hX, ht⟩ => ⟨X₁, X₂, hX, ht⟩⟩

theorem crtBody_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) : WP isa crtBody s (CrtOut g s v) := by
  unfold crtBody
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (start_ok' h) fun u ⟨_, hu⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono hu fun t1 h1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  exact WP.mono (divN_ctx_ok h1) fun t2 h2 => crtChecks_ok' h2

/-! ## The checks of `d` -/

/-- The mask before the checks of `d`. -/
abbrev cMask (v : Vals) (X₁ X₂ R₁ R₂ R₃ : Nat) : Bool :=
  VG.Proof.Rsa.crtBits v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃

/-- After the division of `d` by `p - 1`. -/
def DivP (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Xq Y₁,
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2)) ∧ Xq = v.d / (2 * (v.p / 2))) ∧
  StgD g s0 (upd (upd (aFin v) aVQ Xq) aVR Y₁) (aVR :: aVQ :: liveFin) (c && decide (v.d < v.n)) t

def DivP' (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Xq Y₁,
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2)) ∧ Xq = v.d / (2 * (v.p / 2))) ∧
  Stg g s0 (upd (upd (aFin v) aVQ Xq) aVR Y₁) (aVR :: aVQ :: liveFin) (c && decide (v.d < v.n)) t

/-- After the division of `d` by `q - 1`. -/
def DivQ (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Y₁ Xq Y₂,
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧
  (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2)) ∧ Xq = v.d / (2 * (v.q / 2))) ∧
  StgD g s0 (upd (upd (aFin v) aVQ Xq) aVR Y₂) (aVR :: aVQ :: liveFin)
    (c && decide (v.d < v.n) && decide (Y₁ = v.dP)) t

def DivQ' (g : Geo) (s0 : State) (v : Vals) (c : Bool) (t : State) : Prop := ∃ Y₁ Xq Y₂,
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧
  (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2)) ∧ Xq = v.d / (2 * (v.q / 2))) ∧
  Stg g s0 (upd (upd (aFin v) aVQ Xq) aVR Y₂) (aVR :: aVQ :: liveFin)
    (c && decide (v.d < v.n) && decide (Y₁ = v.dP)) t

/-- After `keyBody`. -/
def KeyOut (g : Geo) (s0 : State) (v : Vals) (t : State) : Prop := ∃ X₁ X₂ R₁ R₂ R₃ Y₁ Y₂,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧ ProdsOk g v R₁ R₂ R₃ ∧
  (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧ (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2))) ∧
  ∃ A live, Stg g s0 A live
    (VG.Proof.Rsa.keyBits' v.n v.d v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃ Y₁ Y₂) t

theorem dChecks1_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : Stg g s0 (aFin v) liveFin c s) :
    WP isa dChecks1 s fun u => VG.Proof.Rsa.Arm.Div.Context (gDiv g) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (DivP g s0 v c) := by
  unfold dChecks1
  rw [wp_seqs_append (by simp [ltA]) (by simp [divSet])]
  refine WP.mono (h.ltA_ok (a := aD) (b := aN) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  exact WP.mono (h1.divSet_ok (a := aD) (d := aM1) (by decide) (by decide) (by decide))
    fun u ⟨cu, wu⟩ => ⟨cu, WP.mono wu fun t ⟨Xq, Xr, hv, ht⟩ => ⟨Xq, Xr, fun pos => hv pos, ht⟩⟩

theorem divP_ctx_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : DivP g s0 v c s) :
    WP isa (.block ctxDiv) s (DivP' g s0 v c) := by
  obtain ⟨Xq, Y₁, hY, h⟩ := h
  exact WP.mono h.ctx_ok fun t ht => ⟨Xq, Y₁, hY, ht⟩

theorem dChecks2_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : DivP' g s0 v c s) :
    WP isa dChecks2 s fun u => VG.Proof.Rsa.Arm.Div.Context (gDiv g) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (DivQ g s0 v c) := by
  obtain ⟨Xq, Y₁, hY, h⟩ := h
  unfold dChecks2
  rw [wp_seqs_append (by simp [eqA]) (by simp [divSet])]
  refine WP.mono (h.eqA_ok (a := aVR) (b := aDP) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  have h1' := (h1.sub (live' := liveFin) (by decide)).congr (A' := aFin v) rfl
  exact WP.mono (h1'.divSet_ok (a := aD) (d := aM2) (by decide) (by decide) (by decide))
    fun u ⟨cu, wu⟩ => ⟨cu, WP.mono wu fun t ⟨Xq', Y₂, hv, ht⟩ =>
      ⟨Y₁, Xq', Y₂, fun pos => (hY pos).1, fun pos => hv pos, ht⟩⟩

theorem divQ_ctx_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : DivQ g s0 v c s) :
    WP isa (.block ctxDiv) s (DivQ' g s0 v c) := by
  obtain ⟨Y₁, Xq, Y₂, h1, h2, h⟩ := h
  exact WP.mono h.ctx_ok fun t ht => ⟨Y₁, Xq, Y₂, h1, h2, ht⟩

theorem dChecks3_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : DivQ' g s0 v c s) :
    WP isa dChecks3 s fun t => ∃ Y₁ Y₂, (0 < 2 * (v.p / 2) → Y₁ = v.d % (2 * (v.p / 2))) ∧
      (0 < 2 * (v.q / 2) → Y₂ = v.d % (2 * (v.q / 2))) ∧
      ∃ A live, Stg g s0 A live (c && decide (v.d < v.n) && decide (Y₁ = v.dP) && decide (Y₂ = v.dQ)) t := by
  obtain ⟨Y₁, Xq, Y₂, h1, h2, h⟩ := h
  exact WP.mono (h.eqA_ok (a := aVR) (b := aDQ) (by decide) (by decide) (by decide))
    fun t ht => ⟨Y₁, Y₂, h1, fun pos => (h2 pos).1, _, _, ht⟩

theorem keyBody_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) : WP isa keyBody s (KeyOut g s v) := by
  unfold keyBody
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (crtBody_ok h) fun t1 ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, h1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dChecks1_ok h1) fun u1 ⟨_, w1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono w1 fun t2 h2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (divP_ctx_ok h2) fun t3 h3 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dChecks2_ok h3) fun u2 ⟨_, w2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono w2 fun t4 h4 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (divQ_ctx_ok h4) fun t5 h5 => ?_
  exact WP.mono (dChecks3_ok h5) fun t ⟨Y₁, Y₂, hY₁, hY₂, A, live, ht⟩ =>
    ⟨X₁, X₂, R₁, R₂, R₃, Y₁, Y₂, hX, hR, hY₁, hY₂, A, live, ht⟩

end VG.Proof.Rsa.Arm.KeyCheck

end

end

/-! # The checks of an RSA key on ARMv7: constant time

Two runs of the checks, each from its own state and numbers, are related at
every step by what correctness says of each (`LiftB`), for a caller's index
`a` (the function's initial state) related by `Pub` across the runs, which
determines the working space and the modulus' length `gf a`. The pieces the
taint analysis checks (`KcTaint.lean`) agree on the registers that
correctness determines from `gf a`, and the divisions start from the same
geometry (`Div.code_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- What the checks of `d` keep from `crtBody`. -/
def CrtKept (g : Geo) (v : Vals) (P : Bool → Prop) : Prop := ∃ X₁ X₂ R₁ R₂ R₃,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧ ProdsOk g v R₁ R₂ R₃ ∧ P (cMask v X₁ X₂ R₁ R₂ R₃)

section
variable {α : Type} (Pub : α → α → Prop)

/-- Two runs at the same step: each from its index `a`, the state `σ` the
checks started from, and its numbers `v`. -/
def LiftB (F : α → State → Vals → State → Prop) (s t : State) : Prop :=
  ∃ a₁ σ₁ v₁ a₂ σ₂ v₂, Pub a₁ a₂ ∧ F a₁ σ₁ v₁ s ∧ F a₂ σ₂ v₂ t

variable {Pub}

theorem LiftB.mono {F G : α → State → Vals → State → Prop} (h : ∀ a σ v s, F a σ v s → G a σ v s) {s t : State} :
    LiftB Pub F s t → LiftB Pub G s t :=
  fun ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ => ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h _ _ _ _ h₁, h _ _ _ _ h₂⟩

/-- A piece the taint analysis checks with the registers `rs` public. -/
theorem pieceB {F G : α → State → Vals → State → Prop} {c : Prog isa} (rs : List Reg)
    (hc : ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true)
    (regs : ∀ a₁ σ₁ v₁ a₂ σ₂ v₂ s t, Pub a₁ a₂ → F a₁ σ₁ v₁ s → F a₂ σ₂ v₂ t → ∀ r ∈ rs, s.gpr r = t.gpr r)
    (hw : ∀ a σ v s, F a σ v s → WP isa c s (G a σ v)) : RelCT isa (LiftB Pub F) c (LiftB Pub G) := by
  intro s t tr₁ tr₂ s' t' ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ e₁ e₂
  obtain ⟨_, hc⟩ := hc
  have r := ((RelCT.taint (A := taint) (P := fun s t => F a₁ σ₁ v₁ s ∧ F a₂ σ₂ v₂ t) (Taint.ofRegs rs)
    (fun s t h => Taint.agree_ofRegs (regs _ _ _ _ _ _ _ _ p h.1 h.2)) hc).wp
    (F₁ := G a₁ σ₁ v₁) (F₂ := G a₂ σ₂ v₂) fun s t h => ⟨hw _ _ _ _ h.1, hw _ _ _ _ h.2⟩)
    s t tr₁ tr₂ s' t' ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, a₁, σ₁, v₁, a₂, σ₂, v₂, p, r.2.2.1, r.2.2.2⟩

/-- A division, from the same geometry in both runs. -/
theorem divPieceB {gf : α → Geo} (hg : ∀ a₁ a₂, Pub a₁ a₂ → gf a₁ = gf a₂) {G : α → State → Vals → State → Prop} :
    RelCT isa (LiftB Pub fun a σ v u => VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a)) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (G a σ v)) VG.Impl.Rsa.Arm.Div.code (LiftB Pub G) := by
  intro s t tr₁ tr₂ s' t' ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ e₁ e₂
  have r := (((VG.Proof.Rsa.Arm.Div.code_ct (g := gDiv (gf a₁))).mono
    (P' := fun s t => (VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a₁)) s ∧
        WP isa VG.Impl.Rsa.Arm.Div.code s (G a₁ σ₁ v₁)) ∧
      (VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a₁)) t ∧ WP isa VG.Impl.Rsa.Arm.Div.code t (G a₂ σ₂ v₂)))
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h).wp
    (F₁ := G a₁ σ₁ v₁) (F₂ := G a₂ σ₂ v₂) fun _ _ h => ⟨h.1.2, h.2.2⟩) s t tr₁ tr₂ s' t'
    ⟨⟨h₁.1, h₁.2⟩, ⟨by rw [hg _ _ p]; exact h₂.1, h₂.2⟩⟩ e₁ e₂
  exact ⟨r.1, a₁, σ₁, v₁, a₂, σ₂, v₂, p, r.2.2.1, r.2.2.2⟩

/-- `r7`–`r9` in two states of `Ws` on the same working space. -/
theorem ws_regs {s t : State} {g : Geo} (h₁ : Ws s g.B g.Z g.w nArr) (h₂ : Ws t g.B g.Z g.w nArr) :
    ∀ r ∈ [Reg.r7, .r8, .r9], s.gpr r = t.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · rw [h₁.r7, h₂.r7]
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]

variable {gf : α → Geo} (hg : ∀ a₁ a₂, Pub a₁ a₂ → gf a₁ = gf a₂) (X : α → State → Prop)
include hg

theorem crtBody_ct : RelCT isa (LiftB Pub fun a σ v s => s = σ ∧ X a σ ∧ BodyIn (gf a) v s) crtBody
    (LiftB Pub fun a σ v t => X a σ ∧ CrtOut (gf a) σ v t) := by
  unfold crtBody
  simp only [seqs]
  refine RelCT.seq (pieceB (G := fun a σ v u => X a σ ∧ VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a)) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (DivN (gf a) σ v)) [.r8, .r11] start_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p h₁ h₂ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.2.2.r8, h₂.2.2.r8, hg _ _ p]
      · rw [h₁.2.2.r11, h₂.2.2.r11, hg _ _ p])
    fun a σ v s ⟨e, x, h⟩ => by subst e; exact WP.mono (start_ok' h) fun u hu => ⟨x, hu⟩) ?_
  refine RelCT.seq ((divPieceB (G := fun a σ v t => X a σ ∧ DivN (gf a) σ v t) hg).mono
    (fun _ _ => LiftB.mono fun _ _ _ _ ⟨x, c, w⟩ => ⟨c, WP.mono w fun _ h => ⟨x, h⟩⟩) fun _ _ h => h) ?_
  refine RelCT.seq (pieceB (G := fun a σ v t => X a σ ∧ DivN' (gf a) σ v t) [.r8] ctxDiv_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, X₁, X₂, _, h₁⟩ ⟨_, Y₁, Y₂, _, h₂⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      rw [h₁.ws.r8, h₂.ws.r8, hg _ _ p])
    fun a σ v s ⟨x, h⟩ => WP.mono (divN_ctx_ok h) fun _ h' => ⟨x, h'⟩) ?_
  exact pieceB (G := fun a σ v t => X a σ ∧ CrtOut (gf a) σ v t) [.r7, .r8, .r9] crtChecks_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, X₁, X₂, _, h₁⟩ ⟨_, Y₁, Y₂, _, h₂⟩ =>
      ws_regs h₁.ws (by rw [hg _ _ p]; exact h₂.ws))
    fun a σ v s ⟨x, h⟩ => WP.mono (crtChecks_ok' h) fun _ h' => ⟨x, h'⟩

theorem keyBody_ct : RelCT isa (LiftB Pub fun a σ v s => s = σ ∧ X a σ ∧ BodyIn (gf a) v s) keyBody
    (LiftB Pub fun a σ v t => X a σ ∧ KeyOut (gf a) σ v t) := by
  unfold keyBody
  simp only [seqs]
  refine RelCT.seq (crtBody_ct hg X) ?_
  refine RelCT.seq (pieceB (G := fun a σ v u => X a σ ∧ CrtKept (gf a) v fun c =>
      VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a)) u ∧ WP isa VG.Impl.Rsa.Arm.Div.code u (DivP (gf a) σ v c))
    [.r7, .r8, .r9] dChecks1_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, h₂⟩ =>
      ws_regs h₁.ws (by rw [hg _ _ p]; exact h₂.ws))
    fun a σ v s ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩ =>
      WP.mono (dChecks1_ok h) fun _ h' => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h'⟩) ?_
  refine RelCT.seq ((divPieceB (G := fun a σ v t => X a σ ∧ CrtKept (gf a) v fun c => DivP (gf a) σ v c t)
    hg).mono (fun _ _ => LiftB.mono fun _ _ _ _ ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, c, w⟩ := k
      exact ⟨c, WP.mono w fun _ h => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩⟩) fun _ _ h => h) ?_
  refine RelCT.seq (pieceB (G := fun a σ v t => X a σ ∧ CrtKept (gf a) v fun c => DivP' (gf a) σ v c t) [.r8]
    ctxDiv_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, _, _, _, h₂⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      rw [h₁.ws.r8, h₂.ws.r8, hg _ _ p])
    fun a σ v s ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩ := k
      exact WP.mono (divP_ctx_ok h) fun _ h' => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h'⟩) ?_
  refine RelCT.seq (pieceB (G := fun a σ v u => X a σ ∧ CrtKept (gf a) v fun c =>
      VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a)) u ∧ WP isa VG.Impl.Rsa.Arm.Div.code u (DivQ (gf a) σ v c))
    [.r7, .r8, .r9] dChecks2_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, _, _, _, h₂⟩ =>
      ws_regs h₁.ws (by rw [hg _ _ p]; exact h₂.ws))
    fun a σ v s ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩ := k
      exact WP.mono (dChecks2_ok h) fun _ h' => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h'⟩) ?_
  refine RelCT.seq ((divPieceB (G := fun a σ v t => X a σ ∧ CrtKept (gf a) v fun c => DivQ (gf a) σ v c t)
    hg).mono (fun _ _ => LiftB.mono fun _ _ _ _ ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, c, w⟩ := k
      exact ⟨c, WP.mono w fun _ h => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩⟩) fun _ _ h => h) ?_
  refine RelCT.seq (pieceB (G := fun a σ v t => X a σ ∧ CrtKept (gf a) v fun c => DivQ' (gf a) σ v c t) [.r8]
    ctxDiv_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h₁⟩
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h₂⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      rw [h₁.ws.r8, h₂.ws.r8, hg _ _ p])
    fun a σ v s ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩ := k
      exact WP.mono (divQ_ctx_ok h) fun _ h' => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h'⟩) ?_
  exact pieceB (G := fun a σ v t => X a σ ∧ KeyOut (gf a) σ v t) [.r7, .r8, .r9] dChecks3_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h₁⟩
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h₂⟩ => ws_regs h₁.ws (by rw [hg _ _ p]; exact h₂.ws))
    fun a σ v s ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩ := k
      exact WP.mono (dChecks3_ok h) fun _ ⟨Y₁, Y₂, hY₁, hY₂, A, live, ht⟩ =>
        ⟨x, X₁, X₂, R₁, R₂, R₃, Y₁, Y₂, hX, hR, hY₁, hY₂, A, live, ht⟩

end

end VG.Proof.Rsa.Arm.KeyCheck

end

end

/-! # The checks of an RSA key on ARMv7: a function is constant time

`fn_ct`: two runs from initial states that agree on what the contracts make
public (`PubF`: the pointers, the lengths, `n` and `e`) are related at every
step by what correctness says of each run (`LiftB`); the entry and the
restore read the stack arguments (`argTaint`), the other pieces the
registers correctness determines, the checks of `n` and `e` branch alike as
both are public, `exponentCheck` is `exponentCheck_ct`, and the checks are
the body's own.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

/-- What two runs' initial states agree on. -/
structure PubF (nA : Nat) (σ₁ σ₂ : State) : Prop where
  sp : σ₁.sp = σ₂.sp
  n : Spec.Rsa.bytesAt σ₁.mem (State.addr (σ₁.gpr .r0)) (fK σ₁) =
    Spec.Rsa.bytesAt σ₂.mem (State.addr (σ₂.gpr .r0)) (fK σ₂)
  e : eBytes σ₁ = eBytes σ₂
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  args : ∀ i < nA, stackArg σ₁ i = stackArg σ₂ i

section
variable {nA iS : Nat} {ins : List (Nat × Nat)}

theorem PubF.geo_eq {σ₁ σ₂ : State} (p : PubF nA σ₁ σ₂) (h : iS + 1 < nA) : geo iS σ₁ = geo iS σ₂ := by
  unfold geo fK
  rw [p.args iS (by omega_using [h]), p.args (iS + 1) h, p.r1]

theorem PubF.nV {σ₁ σ₂ : State} (p : PubF nA σ₁ σ₂) : nV σ₁ = nV σ₂ := congrArg Spec.Rsa.os2ip p.n
theorem PubF.eV {σ₁ σ₂ : State} (p : PubF nA σ₁ σ₂) : eV σ₁ = eV σ₂ := congrArg Spec.Rsa.os2ip p.e
theorem PubF.K {σ₁ σ₂ : State} (p : PubF nA σ₁ σ₂) : fK σ₁ = fK σ₂ := by simp only [fK, p.r1]

/-- What makes a state of a run agree with the other's on the stack arguments. -/
structure RunF (nA iS : Nat) (ins : List (Nat × Nat)) (σ s : State) : Prop where
  pre : FnPre nA iS ins σ
  sp : s.sp = σ.sp
  wr : s.wr = σ.wr
  args : ∀ i < nA, stackArg s i = stackArg σ i

theorem FnBase.run {σ s : State} (h : FnBase nA iS ins σ s) : RunF nA iS ins σ s :=
  ⟨h.pre, h.sp, h.wr, fun _ hi => h.arg hi⟩

theorem RunF.wf {σ s : State} (h : RunF nA iS ins σ s) :
    s.sp.toNat + 4 * nA ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4 * nA⟩ r := by
  refine ⟨by rw [h.sp]; exact h.pre.sp, ?_⟩
  have e : (⟨State.addr s.sp, 4 * nA⟩ : Region) = rA nA σ := by
    simp only [rA, stackArgAddr, h.sp, Nat.mul_zero, BitVec.add_zero]
  rw [e, h.wr, h.pre.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact h.pre.sA.symm

theorem agreeF {σ₁ σ₂ s₁ s₂ : State} (p : PubF nA σ₁ σ₂) (h₁ : RunF nA iS ins σ₁ s₁)
    (h₂ : RunF nA iS ins σ₂ s₂) {rs : List Reg} (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.Arm.Taint.Agree (argTaint rs (4 * nA)) s₁ s₂ := by
  have hsp : s₁.sp = s₂.sp := by rw [h₁.sp, h₂.sp, p.sp]
  exact agree_argTaint hr hsp h₁.wf h₂.wf
    (argMem_of (j := nA) hsp (by rw [h₁.sp]; exact h₁.pre.sp) fun i hi => by
      rw [h₁.args i hi, h₂.args i hi, p.args i hi])

/-- A piece the taint analysis checks from the stack arguments and the registers `rs`. -/
theorem pieceF {G H : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hc : ∃ hc, (VG.Taint.check taint (argTaint rs (4 * nA)) c hc).isSome = true)
    (run : ∀ a s, G a s → RunF nA iS ins a s)
    (regs : ∀ a₁ a₂ s t, PubF nA a₁ a₂ → G a₁ s → G a₂ t → ∀ r ∈ rs, s.gpr r = t.gpr r)
    (hw : ∀ a s, G a s → WP isa c s (H a)) :
    RelCT isa (LiftB (PubF nA) fun a _ _ s => G a s) c (LiftB (PubF nA) fun a _ _ t => H a t) := by
  intro s t tr₁ tr₂ s' t' ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ e₁ e₂
  have r := rel_agree (F := G a₁) (F' := G a₂) (G := H a₁) (G' := H a₂) (argTaint rs (4 * nA))
    (fun _ _ h h' => agreeF p (run _ _ h) (run _ _ h') (regs _ _ _ _ p h h')) hc (hw a₁) (hw a₂)
    s t tr₁ tr₂ s' t' ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, a₁, σ₁, v₁, a₂, σ₂, v₂, p, r.2.1, r.2.2⟩

/-- As `pieceF`, for pieces whose facts depend on where the checks started and on the numbers. -/
theorem pieceFB {F G : State → State → Vals → State → Prop} {c : Prog isa} (rs : List Reg)
    (hc : ∃ hc, (VG.Taint.check taint (argTaint rs (4 * nA)) c hc).isSome = true)
    (run : ∀ a σ v s, F a σ v s → RunF nA iS ins a s)
    (regs : ∀ a₁ σ₁ v₁ a₂ σ₂ v₂ s t, PubF nA a₁ a₂ → F a₁ σ₁ v₁ s → F a₂ σ₂ v₂ t → ∀ r ∈ rs, s.gpr r = t.gpr r)
    (hw : ∀ a σ v s, F a σ v s → WP isa c s (G a σ v)) :
    RelCT isa (LiftB (PubF nA) F) c (LiftB (PubF nA) G) := by
  intro s t tr₁ tr₂ s' t' ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ e₁ e₂
  have r := rel_agree (F := F a₁ σ₁ v₁) (F' := F a₂ σ₂ v₂) (G := G a₁ σ₁ v₁) (G' := G a₂ σ₂ v₂)
    (argTaint rs (4 * nA))
    (fun _ _ h h' => agreeF p (run _ _ _ _ h) (run _ _ _ _ h') (regs _ _ _ _ _ _ _ _ p h h')) hc
    (hw a₁ σ₁ v₁) (hw a₂ σ₂ v₂) s t tr₁ tr₂ s' t' ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, a₁, σ₁, v₁, a₂, σ₂, v₂, p, r.2.1, r.2.2⟩

/-- The registers of two states of `Mid` agree on `r8`. -/
theorem mid_r8 {a₁ a₂ s t : State} {A₁ A₂ : Nat → Nat} (h : iS + 1 < nA) (p : PubF nA a₁ a₂)
    (h₁ : Mid nA iS ins a₁ s A₁) (h₂ : Mid nA iS ins a₂ t A₂) : ∀ r ∈ [Reg.r8], s.gpr r = t.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  rw [h₁.ws.r8, h₂.ws.r8, p.geo_eq h]

/-- `exponentCheck` in two runs from the same exponent. -/
theorem expPiece :
    RelCT isa (LiftB (PubF nA) fun a _ _ s => Mid nA iS ins a s (aEnt ins a) ∧
        ExponentInput (a.gpr .r2) (eBytes a) s) exponentCheck
      (LiftB (PubF nA) fun a _ _ t => Mid nA iS ins a t (aEnt ins a) ∧
        t.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (eV a)).toNat) := by
  intro s t tr₁ tr₂ s' t' ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ e₁ e₂
  have pos : 0 < (eBytes a₁).length := by
    rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; exact h₁.1.base.pre.e1
  have h₂' : ExponentInput (a₁.gpr .r2) (eBytes a₁) t := by rw [p.r2, p.e]; exact h₂.2
  have r := (((exponentCheck_ct pos).mono
    (P' := fun (u₁ u₂ : State) => (Mid nA iS ins a₁ u₁ (aEnt ins a₁) ∧ ExponentInput (a₁.gpr .r2) (eBytes a₁) u₁) ∧
      (Mid nA iS ins a₂ u₂ (aEnt ins a₂) ∧ ExponentInput (a₂.gpr .r2) (eBytes a₂) u₂ ∧
        ExponentInput (a₁.gpr .r2) (eBytes a₁) u₂))
    (fun _ _ h => ⟨h.1.2, h.2.2.2⟩) fun _ _ h => h).wp
    (F₁ := fun (u : State) => Mid nA iS ins a₁ u (aEnt ins a₁) ∧
      u.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (eV a₁)).toNat)
    (F₂ := fun (u : State) => Mid nA iS ins a₂ u (aEnt ins a₂) ∧
      u.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (eV a₂)).toNat)
    fun _ _ h => ⟨expCheck_ok h.1.1 h.1.2, expCheck_ok h.2.1 h.2.2.1⟩) s t tr₁ tr₂ s' t'
    ⟨h₁, h₂.1, h₂.2, h₂'⟩ e₁ e₂
  exact ⟨r.1, a₁, σ₁, v₁, a₂, σ₂, v₂, p, r.2.2.1, r.2.2.2⟩

theorem fn_ct {body : Prog isa} {vf : State → Vals} (h4 : 4 * iS < 4096) (hS : iS + 1 < nA)
    (hentry : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] (4 * nA))
      (entry (4 * iS) (ins.map fun p => (4 * p.1, p.2))) hc).isSome = true)
    (hrestore : ∃ hc, (VG.Taint.check taint (argTaint [] (4 * nA)) (.block (restore (4 * iS))) hc).isSome = true)
    (hv : ∀ σ, FnPre nA iS ins σ → aEnt ins σ = vals (vf σ))
    (hA : ∀ σ, FnPre nA iS ins σ → ∀ j < nArr, aEnt ins σ j < 2 ^ (32 * (geo iS σ).w))
    (hbody : RelCT isa (LiftB (PubF nA) fun a σ v s => s = σ ∧ FnBase nA iS ins a σ ∧ BodyIn (geo iS a) v s ∧
      v = vf a)
      body (LiftB (PubF nA) fun a σ _ t => FnBase nA iS ins a σ ∧ ∃ A live c, Stg (geo iS a) σ A live c t)) :
    RelCT isa (fun s t => FnPre nA iS ins s ∧ FnPre nA iS ins t ∧ PubF nA s t)
      (fn (4 * iS) (ins.map fun p => (4 * p.1, p.2)) body) fun _ _ => True := by
  unfold fn
  simp only [seqs]
  -- The entry.
  refine RelCT.seq ((pieceF (iS := iS) (ins := ins) (G := fun a s => s = a ∧ FnPre nA iS ins a)
    (H := fun a t => Mid nA iS ins a t (aEnt ins a) ∧ t.z = Spec.Rsa.modulusValid (nV a) (fK a))
    [.r0, .r1, .r2, .r3] hentry (fun a s ⟨e, h⟩ => by subst e; exact ⟨h, rfl, rfl, fun _ _ => rfl⟩)
    (fun a₁ a₂ s t p ⟨e₁, _⟩ ⟨e₂, _⟩ => by
      subst e₁ e₂
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      exacts [p.r0, p.r1, p.r2, p.r3])
    fun a s ⟨e, h⟩ => by subst e; exact entry_ok h h4).mono
      (fun s t ⟨h₁, h₂, p⟩ => ⟨s, s, vf s, t, t, vf t, p, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩⟩) fun _ _ h => h) ?_
  -- The branches, to `FnBase` for `restore`.
  refine RelCT.seq (R := LiftB (PubF nA) fun a _ _ s => FnBase nA iS ins a s) (RelCT.ite ?_ ?_ ?_) ?_
  · rintro s t ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, ⟨_, z₁⟩, ⟨_, z₂⟩⟩
    show some s.z = some t.z
    rw [z₁, z₂, p.nV, p.K]
  · -- `n` is valid: `e` checked.
    refine RelCT.seq (R := LiftB (PubF nA) fun a _ _ s => Mid nA iS ins a s (aEnt ins a) ∧
      s.z = Spec.Rsa.exponentValid (eV a)) ?_ ?_
    · unfold eCheck
      simp only [seqs]
      refine RelCT.seq ((pieceB (G := fun a _ _ s => Mid nA iS ins a s (aEnt ins a) ∧
          ExponentInput (a.gpr .r2) (eBytes a) s) [.r8] eLoad_taint
        (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p h₁ h₂ => mid_r8 hS p h₁.1 h₂.1)
        fun a _ _ s h => eLoad_ok h.1).mono (fun _ _ ⟨h, _⟩ => LiftB.mono (fun _ _ _ _ h => h) h)
          fun _ _ h => h) ?_
      refine RelCT.seq expPiece ?_
      exact pieceB [] eCmp_taint (fun _ _ _ _ _ _ _ _ _ _ _ => by simp)
        fun a _ _ s h => eCmp_ok h.1 h.2
    refine RelCT.ite ?_ ?_ ?_
    · rintro s t ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, ⟨_, z₁⟩, ⟨_, z₂⟩⟩
      show some s.z = some t.z
      rw [z₁, z₂, p.eV]
    · -- Both are valid: the checks, and the mask returned.
      refine RelCT.seq (hbody.mono (fun s t ⟨⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, ⟨h₁, _⟩, ⟨h₂, _⟩⟩, _⟩ =>
        ⟨a₁, s, vf a₁, a₂, t, vf a₂, p, ⟨rfl, h₁.base, h₁.bodyIn _ (hv _ h₁.base.pre) (hA _ h₁.base.pre), rfl⟩,
          ⟨rfl, h₂.base, h₂.bodyIn _ (hv _ h₂.base.pre) (hA _ h₂.base.pre), rfl⟩⟩) fun _ _ h => h) ?_
      exact pieceB [.r8] ret_taint
        (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r rfl
          rw [h₁.ws.r8, h₂.ws.r8, p.geo_eq hS])
        fun a σ _ s ⟨b, A, live, c, h⟩ => WP.mono (ret_ok (b.keep h.keep (fun j hj => List.mem_range.mp hj)
          (by decide) (by decide) h.rest.sp h.rest.rd h.rest.wr) h.ws.r8 h.mask) fun _ h => h.1
    · exact (pieceB [] ret0_taint (fun _ _ _ _ _ _ _ _ _ _ _ => by simp)
        fun a _ _ s h => wp_mov (op2_imm (by decide)) fun u up => WP.block_nil
          (h.1.base.of_rest (up.rest (ws := [.r0]) (by simp)) up.mem)).mono
        (fun _ _ ⟨h, _⟩ => h) fun _ _ h => h
  · -- `n` is not valid.
    exact (pieceB [] ret0_taint (fun _ _ _ _ _ _ _ _ _ _ _ => by simp)
      fun a _ _ s h => wp_mov (op2_imm (by decide)) fun u up => WP.block_nil
        (h.1.base.of_rest (up.rest (ws := [.r0]) (by simp)) up.mem)).mono
      (fun _ _ ⟨h, _⟩ => h) fun _ _ h => h
  · -- `restore`.
    exact (pieceF (iS := iS) (ins := ins) (G := fun a s => FnBase nA iS ins a s) (H := fun _ _ => True) []
      hrestore (fun _ _ h => h.run) (fun _ _ _ _ _ _ _ => by simp)
      fun a s h => WP.mono (restore_ok h h4) fun _ _ => trivial).mono (fun _ _ h => h) fun _ _ _ => trivial

end

end VG.Proof.Rsa.Arm.KeyCheck

end

end

/-! # `vg_rsa_check_crt_key` on ARMv7 is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CheckCrtKey
open VG VG.Arm VG.Proof.Rsa.Arm.KeyCheck VG.Impl.Rsa.Arm.KeyCheck

/-- Two runs that agree on `n`, `e`, the pointers and the lengths. -/
theorem pubF_of {s t : State} (sp : s.sp = t.sp)
    (bytes : (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat ++
        Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (t.gpr .r0)) (t.gpr .r1).toNat ++
        Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (t.gpr .r2)) (t.gpr .r3).toNat).map (·.toNat))
    (p0 : s.gpr .r0 = t.gpr .r0) (p1 : s.gpr .r1 = t.gpr .r1) (p2 : s.gpr .r2 = t.gpr .r2)
    (p3 : s.gpr .r3 = t.gpr .r3) {nA : Nat} (args : ∀ i < nA, stackArg s i = stackArg t i) : PubF nA s t := by
  have b := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 bytes
  obtain ⟨hn, he⟩ := List.append_inj b (by
    rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length, p1])
  exact ⟨sp, hn, he, p0, p1, p2, p3, args⟩

end VG.Proof.Rsa.Arm.CheckCrtKey
