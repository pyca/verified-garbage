module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Exp7
import VerifiedGarbage.Proof.Bignum.Arm.Setup
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint6
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont1
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.Arm.RdTwos
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Base
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Loads
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! ### `Dsa.Arm.Prime.Mont3`, which this module and modules that import it used -/

section

/-! # A candidate on ARMv7: tools for Montgomery multiplication's stages

`KS.of_outZ`: memory changed only outside the working space keeps a stage;
`VP.stk`: a piece of loads and stores relative to the stack;
`St.pctx`: the working space's context restored; `clrTopO_ok`: `clrTop j`
writes only the two words above the number of `[j]`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- Loads, stores and arithmetic relative to the stack pointer. -/
theorem VP.stk {F G : State → State → Prop} {code : List Instr}
    (keep : code.all (fun i => decide (clobbers i .r12 = false)) = true)
    (leak : code.all VG.Proof.Rsa.Arm.stackInstruction = true)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (wp : ∀ σ s, F σ s → WP isa (.block (.addSp .r12 0 :: code)) s (G σ)) :
    VP F (.block (.addSp .r12 0 :: code)) G :=
  VP.of_ct (fun _ _ => (VG.Proof.Rsa.Arm.setupChecked_ct code keep leak).mono
    (fun _ _ h => sp _ _ _ _ h.1 h.2) fun _ _ _ => trivial) wp

section
variable {P : CP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- Memory that changed only in regions apart from the working space. -/
theorem outZ_of_frame {rs : List Region} {m m' : Mem} (f : Frame rs m m')
    (hd : ∀ r ∈ rs, P.rS.Disjoint r) : Outs (State.addr P.B) [(P.Z, 2 ^ 64)] m m' := by
  intro x hx
  have h := hx _ (List.mem_singleton_self _)
  have hz : (x - State.addr P.B).toNat < P.Z := by
    have := (x - State.addr P.B).isLt; simp only [ofs] at h; omega_arith
  refine f x fun r hr hc => ?_
  exact hd r hr x (by simp only [Region.Contains]; omega_arith) hc

/-- Memory that changed only outside the working space keeps a stage. -/
theorem KS.of_outZ (h : KS P σ A live V ls s) (o : Outs (State.addr P.B) [(P.Z, 2 ^ 64)] s.mem t.mem)
    (fr : Frame P.chg σ.mem t.mem) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    KS P σ A live V ls t := by
  have pre := h.pre
  have hz := pre.hdr_Z
  have zl := pre.Z_le
  have sl : ∀ d, d + 4 ≤ hdr → slot t.mem P.B d = slot s.mem P.B d := fun d hd => by
    have := Outs.val32 (k := 1) (d := d) o (fun r hr => by simp at hr; subst hr; left; omega_arith) (by omega_arith)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  refine ⟨pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, fr, (sl 16 (by decide)).trans h.cnt,
    fun j hj => ?_, fun d hd => (sl d (h.ls_ok d hd).1).trans (h.sl d hd), h.live_lt, h.ls_ok⟩
  have := pre.fitZ (h.live_lt j hj)
  have : S P.W = 4 * (P.W + 2) := rfl
  rw [← h.arrs j hj]
  exact Outs.val32 o (fun r hr => by simp at hr; subst hr; left; omega_arith) (by omega_arith)

/-- Frame word 0 written. -/
theorem KS.w0 (h : KS P σ A live V ls s) (v : BitVec 32) (ht : t.mem = s.mem.writeW (State.addr P.sp) v)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : KS P σ A live V ls t := by
  have pre := h.pre
  have hc : P.rW0.Contains (State.addr P.sp) (32 / 8) := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  have f0 : Frame [P.rW0] s.mem t.mem := by rw [ht]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc
  refine h.of_outZ (outZ_of_frame (P := P) f0 fun r hr => ?_) (by rw [ht]; exact h.frame.writeW (by simp) _ hc) sp rd wr
  simp only [List.mem_singleton] at hr; subst hr
  exact pre.sF.sub_right (Offset.sub_base (State.addr P.sp) (d := 0) (n := 4) (k := 88) (by decide) |>
    fun h => by simpa using h)

end

/-- `clrTop j`: the two top words of `[j]` cleared, and nothing else written. -/
theorem clrTopO_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (hw : 2 ≤ w) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Outside (State.addr B) (arr w j + 4 * (w - 2)) 8 s.mem t.mem →
      num t.mem B w j = val32 s.mem (State.addr B) (arr w j) (w - 2) → Rest opRegs s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (clrTop j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  unfold clrTop VG.Impl.Rsa.Arm.Recover.clrTop
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by omega_arith) fun s1 p1 r1 m1 h1 => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have e3 : s3.gpr .r0 = B + BitVec.ofNat 32 (arr w j + 4 * (w - 2)) := by
    rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, h1.r9]
    have : BitVec.ofNat 32 w <<< 2 = BitVec.ofNat 32 (4 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    rw [this, BitVec.add_assoc, ← BitVec.ofNat_add,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega_arith)]
    congr 2; omega_arith
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  have h4 : Ws s4 B Z w N :=
    ((h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)).of_upd u4
      (by decide) (by decide) (by decide)
  have a0 : State.addr (s4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * (w - 2)) := by
    rw [u4.other _ (by decide), e3, BitVec.add_zero]; exact h.addr (by omega_arith)
  refine wp_str (by decide) a0 (h4.write (by omega_arith)) fun s5 u5 => ?_
  have h5 := h4.of_mupd u5
  have a4 : State.addr (s5.gpr .r0 + BitVec.ofNat 32 4) = off (State.addr B) (arr w j + 4 * (w - 2) + 4) := by
    rw [u5.gpr, u4.other _ (by decide), e3, BitVec.add_assoc, ← BitVec.ofNat_add]; exact h.addr (by omega_arith)
  refine wp_str (by decide) a4 (h5.write (by omega_arith)) fun t u6 => ?_
  have ht := h5.of_mupd u6
  have z4 : s4.gpr .r1 = 0 := u4.gpr
  have mt : t.mem = (s.mem.writeW (off (State.addr B) (arr w j + 4 * (w - 2))) (0 : BitVec 32)).writeW
      (off (State.addr B) (arr w j + 4 * (w - 2) + 4)) (0 : BitVec 32) := by
    rw [u6.mem, u5.gpr, z4, u5.mem, z4, u4.mem, u3.mem, u2.mem, m1]
  have o1 := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * (w - 2)) (0 : BitVec 32) (by omega_arith)
  have o2 := writeW32_outside (s.mem.writeW (off (State.addr B) (arr w j + 4 * (w - 2))) (0 : BitVec 32))
    (State.addr B) (d := arr w j + 4 * (w - 2) + 4) (0 : BitVec 32) (by omega_arith)
  rw [← mt] at o2
  refine k t ht ((o1.mono (Nat.le_refl _) (by omega_arith)).trans (o2.mono (by omega_arith) (by omega_arith))) ?_
    ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
    ((u4.rest (by simp)).trans ((u5.rest _).trans (u6.rest _))))))
  change val32 _ _ _ _ = _
  have e := val32_append t.mem (State.addr B) (arr w j) (w - 2) 2
  rw [show w - 2 + 2 = w by omega_arith] at e
  have t0 : w32 t.mem (State.addr B) (arr w j + 4 * (w - 2)) = 0 := by
    simp only [w32]
    rw [mt, Mem.readW_writeW_sep (w := 32) (w' := 32) (Offset.sep _ (d := arr w j + 4 * (w - 2)) (n := 4)
      (e := arr w j + 4 * (w - 2) + 4) (k := 4) (Or.inl (Nat.le_refl _)) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self32]; rfl
  have t1 : w32 t.mem (State.addr B) (arr w j + 4 * (w - 2) + 4) = 0 := by
    simp only [w32]; rw [mt, Mem.readW_writeW_self32]; rfl
  have top : val32 t.mem (State.addr B) (arr w j + 4 * (w - 2)) 2 = 0 := by
    simp only [val32, t0, t1]
  rw [e, top, Nat.mul_zero, Nat.add_zero]
  exact (o2.val32 (by omega_arith) (by omega_arith)).trans (o1.val32 (by omega_arith) (by omega_arith))

end VG.Proof.Dsa.Arm.Prime

end

end

/-! # A candidate on ARMv7: Montgomery multiplication's base and header

`montSet`: its base into frame word 0 and `r0`, `w` into `r7`
(`montSet_vp`); `setup` (`setup_vp`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The stage of the exponent, as a stage of the key working space alone. -/
abbrev KX (P : CP) (E : State → Prop) (L : List Nat) (σ s : State) : Prop :=
  E σ ∧ KS P σ (AX P σ) L (V3 P σ) [sUsed] s

/-- Before `setup`. -/
abbrev SB (P : CP) (E : State → Prop) (σ s : State) : Prop :=
  KX P E LX σ s ∧ s.gpr .r0 = P.M0 ∧ s.gpr .r7 = BitVec.ofNat 32 P.w ∧ s.gpr .r3 = 0 ∧
    s.mem.readW (State.addr P.sp) 32 = P.M0

/-- After `setup`. -/
abbrev SC (P : CP) (E : State → Prop) (σ s : State) : Prop :=
  KX P E LX σ s ∧ Layout s.mem (State.addr P.M0) P.lenM ∧ wOf s.mem (State.addr P.M0) = P.w ∧
    s.gpr .r0 = P.M0 ∧ s.mem.readW (State.addr P.sp) 32 = P.M0

section
variable {P : CP}

theorem montSet_eq : montSet = (ptr .r0 mBase ++ ([.dp .sub .r0 .r0 (.imm 256)] : List Instr)) ++
    (.addSp .r12 0 :: [.str .r0 .r12 0, .ldrSp .r7 foL, .mov .r7 (.shifted .r7 .lsr 3), .mov .r3 (.imm 0)]) := rfl

theorem In.rW0_rS {σ : State} (pre : In P σ) : P.rS.Disjoint P.rW0 :=
  pre.sF.sub_right (Offset.sub_base (State.addr P.sp) (d := 0) (n := 4) (k := 88) (by decide) |>
    fun h => by simpa using h)

/-- `montSet`. -/
theorem montSet_vp {E : State → Prop} : VP (SX P E) (.block montSet) (SB P E) := by
  rw [montSet_eq]
  refine VP.block_append (G := fun σ s => SX P E σ s ∧ s.gpr .r0 = P.M0)
    (VP.kv montHead_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_) ?_
  · have pre := h.pre
    refine ptr_ok hw (r := .r0) (by decide) (by decide) fun s1 p1 r1 m1 hw1 => ?_
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => WP.block_nil ⟨⟨e, ?_, ?_⟩, ?_⟩
    · exact h.of_rest ((r1.mono (by simp)).trans (u2.rest (ws := [.r0]) (by simp))) (u2.mem.trans m1)
    · exact hw1.of_upd u2 (by decide) (by decide) (by decide)
    · have e := pre.oM_eq
      have hm : arr P.W mBase - 256 = P.oM := by omega_using [e]
      rw [u2.gpr, dpVal, p1, show (256 : BitVec 32) = BitVec.ofNat 32 256 from rfl,
        VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega_using [e]), hm]
  · refine VP.stk (by decide) (by decide) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, r0⟩ => ?_
    · rw [h₁.1.2.1.sp, h₁.1.2.1.pre.sp, h₂.1.2.1.sp, h₂.1.2.1.pre.sp]
    have pre := h.pre
    have spf := pre.spFit
    have sp : s.sp = P.sp := h.sp.trans pre.sp
    refine wp_stackAddr (r := .r12) (d := 0) (by decide) fun u1 h1 => ?_
    refine wp_str (a := State.addr P.sp) (by decide)
      (by rw [h1.gpr, sp, BitVec.add_zero, BitVec.add_zero]) ⟨P.rFr,
        by rw [h1.wr, h.wr, pre.wr]; simp, by
          simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩ fun u2 m2 => ?_
    have v0 : u1.gpr .r0 = P.M0 := by rw [h1.other _ (by decide), r0]
    have h2 := h.w0 (P.M0) (by rw [m2.mem, h1.mem, v0]) (by rw [m2.sp, h1.sp]) (by rw [m2.rd, h1.rd])
      (by rw [m2.wr, h1.wr])
    have sv : u2.mem.readW (State.addr P.sp) 32 = P.M0 := by
      rw [m2.mem, Mem.readW_writeW_self32, v0]
    refine h2.ldrSp (o := foL) (by decide) fun u3 v3 => ?_
    rw [pre.wL] at v3
    refine wp_mov (op2_lsr (by decide)) fun u4 v4 => wp_mov (op2_imm (by decide)) fun t v5 => WP.block_nil ?_
    have r5 : Rest [.r7, .r3] u2 t := (v3.rest (by simp)).trans ((v4.rest (by simp)).trans (v5.rest (by simp)))
    have m5 : t.mem = u2.mem := by rw [v5.mem, v4.mem, v3.mem]
    refine ⟨⟨e, h2.of_rest r5 m5⟩, ?_, ?_, v5.gpr, by rw [m5]; exact sv⟩
    · rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), m2.gpr, v0]
    · rw [v5.other _ (by decide), v4.gpr, v3.gpr]
      apply BitVec.eq_of_toNat_eq
      have := pre.k2
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      simp only [CP.w]; omega_using [this]

/-- `setup`. -/
theorem setup_vp {E : State → Prop} : VP (SB P E) VG.Impl.Bignum.Arm.setup (SC P E) := by
  refine VP.of_ct (fun σ₁ σ₂ s t tr1 tr2 u v h e1 e2 =>
    ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.1.2.1.trans h.2.2.1.symm) e1 e2, trivial⟩)
    fun σ s ⟨⟨e, h⟩, r0, r7, r3, sv⟩ => ?_
  have pre := h.pre
  have hw := pre.w4
  refine WP.mono (setup_ok s (pre.workspaceM h.wr) (by omega_using [hw]) (by omega_using [hw])
    (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes, CP.lenM]; omega_using []) r0 r7 r3)
    fun t ⟨lay, wd, t0, outs, rest⟩ => ⟨⟨e, ?_⟩, lay, wd, t0, ?_⟩
  · have f := frame_of_outs (n := 256) outs (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> decide)
    have k := keep_of_frameH pre f
    refine h.core k (by simp only [List.mem_range'_1]; intro j hj; simp only [nArr]; omega_using [hj]) (by simp) rest.sp rest.rd
      rest.wr (h.arrs_keep k (fun j hj hj' => by
        simp only [List.mem_range'_1] at hj'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [mBase, aCm1, aTwo, aOne, aC] at hj' <;> omega)
        (by simp)) (h.sl_keep k (by simp) (by simp)) h.live_lt h.ls_ok
  · have f := frame_of_outs (n := 256) outs (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> decide)
    rw [← sv]
    refine f.readW (r := P.rW0) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    refine pre.rW0_rM.sub_right ?_
    show Region.Sub ⟨State.addr P.M0, 256⟩ ⟨State.addr P.M0, 8 * P.lenM⟩
    have := Offset.sub_base (State.addr P.M0) (d := 0) (n := 256) (k := 8 * P.lenM) (by simp only [CP.lenM]; omega_using [])
    simpa only [BitVec.add_zero] using this

end

end VG.Proof.Dsa.Arm.Prime
