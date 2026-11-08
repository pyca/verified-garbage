module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyCT
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.WindowRhs
import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldTest
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
import VerifiedGarbage.Proof.Ed25519.PPC64LE.WindowDigit
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Ed25519.WindowNibble
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.Ed25519.PPC64LE.DecodeCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyCT
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.WindowRhs
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldTest
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.WindowDigit
meta import VerifiedGarbage.Proof.Ed25519.Window
meta import VerifiedGarbage.Proof.Ed25519.WindowNibble
meta import VerifiedGarbage.Proof.Ed25519.Group.Decode
meta import VerifiedGarbage.Proof.Ed25519.ScalarBytes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.DecodeCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Verification's windows on PPC64LE leak only the inputs

`verifyRhs` branches, and addresses its tables, on digits it loads from the
challenge and the signature, which the taint analysis takes as secret: each
such branch and address is related by correctness instead, as both runs load
the same digit of the same scalars (`addA_ct`, `addB_ct`, `windowB_ct`). The
code between them is the taint analysis's (`ctRegs`). The windows' count is
the challenge's (`windowCount_ok`), and the comparison branches on the group
elements the two sums represent, the same in both runs (`pointEqualRep_ct`).
Together: `rhs_ct`, which is `RhsCT`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Proof.Ed25519 (Rep RepP baseAff dZ)
open VG.Spec.Ed25519 (decodeLE bytesAt)
open Edwards

/-- An `ite` whose condition each run evaluates to the same `v`. -/
theorem ct_ite {A : State → Prop} {c : isa.Cond} {th el : Prog isa} (v : Bool)
    (hv : ∀ s, A s → isa.eval c s = some v) (ht : v = true → RelCT isa (Both A) th fun _ _ => True)
    (he : v = false → RelCT isa (Both A) el fun _ _ => True) :
    RelCT isa (Both A) (.ite c th el) fun _ _ => True := by
  refine RelCT.ite (fun _ _ h => by rw [hv _ h.1, hv _ h.2]) ?_ ?_
  · cases v
    · exact RelCT.of_false fun _ _ h => by have e := h.2; rw [hv _ h.1.1] at e; cases e
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases v
    · exact (he rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun _ _ h => by have e := h.2; rw [hv _ h.1.1] at e; cases e

/-- Two pieces, with what the first gives each run. -/
theorem ct_seq {A B : State → Prop} {c₁ c₂ : Prog isa} (h₁ : RelCT isa (Both A) c₁ fun _ _ => True)
    (hw : ∀ s, A s → WP isa c₁ s B) (h₂ : RelCT isa (Both B) c₂ fun _ _ => True) :
    RelCT isa (Both A) (.seq c₁ c₂) fun _ _ => True :=
  RelCT.seq (ctBoth h₁ hw) h₂

section
variable {b sp : Addr}

/-! ## The comparison, by the group elements -/

/-- Before the comparison: slots 0–3 and 4–7 representing `P` and `Q`. -/
def EqRepPre (b sp : Addr) (P Q : EPoint dZ) (s : State) : Prop :=
  Pin b sp s ∧ RepP (point (env s.mem b) 0 1 2 3) P ∧ RepP (point (env s.mem b) 4 5 6 7) Q

theorem pointEqualRep_ct (P Q : EPoint dZ) :
    RelCT isa (Both (EqRepPre b sp P Q)) Impl.Ed25519.PPC64LE.pointEqual fun _ _ => True := by
  unfold Impl.Ed25519.PPC64LE.pointEqual
  let E (t : State) : Prop := Pin b sp t ∧ (env t.mem b 8 = env t.mem b 9 ↔ P.x = Q.x) ∧
    (env t.mem b 10 = env t.mem b 11 ↔ P.y = Q.y)
  have h1 := ctBoth (ctRegs [.r6] (A := EqRepPre b sp P Q) (c := fieldCode pointEqualOps)
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide)) (B := E) fun s h =>
      WP.mono (fieldCode_ok _ h.1.1.ctx) fun t ⟨k, e⟩ => by
        refine ⟨h.1.of_rest k.rest (by decide), ?_, ?_⟩
        · rw [e]; exact Proof.Ed25519.repP_cross_x h.2.1 h.2.2
        · rw [e]; exact Proof.Ed25519.repP_cross_y h.2.1 h.2.2
  let E' (t : State) : Prop := Pin b sp t ∧ (env t.mem b 10 = env t.mem b 11 ↔ P.y = Q.y)
  have h2 := ctBoth (ctRegs [.r6] (A := E) (c := fieldEqual 8 9) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => E' t ∧ (t.gpr .r5 = 0 ↔ P.x = Q.x)) fun s h =>
      WP.mono (fieldEqual_ok h.1.1.ctx 8 9) fun t ⟨k, e, z⟩ =>
        ⟨⟨h.1.of_rest k.rest (by decide), by rw [e]; exact h.2.2⟩, z.trans h.2.1⟩
  have h3 := ctBoth (ctRegs [.r6] (A := E') (c := fieldEqual 10 11) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => Pin b sp t ∧ (t.gpr .r5 = 0 ↔ P.y = Q.y)) fun s h =>
      WP.mono (fieldEqual_ok h.1.1.ctx 10 11) fun t ⟨k, _, z⟩ =>
        ⟨h.1.of_rest k.rest (by decide), z.trans h.2⟩
  refine RelCT.seq h1 (RelCT.seq h2 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_))
  · refine RelCT.seq (h3.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
      (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
    · exact (ctRegs [.r6] (A := Pin b sp) (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)).mono
        (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h

end

section
variable {b sp pk sig ch T : Addr} {A : Spec.Ed25519.Point} {K S : Nat}

/-! ## A window -/

/-- The registers both runs agree on, within a window. -/
theorem wregs {s₁ s₂ : State} (h₁ : WCtx b pk sig ch T A K S s₁) (h₂ : WCtx b pk sig ch T A K S s₂)
    (p₁ : s₁.sp = sp) (p₂ : s₂.sp = sp) {x : BitVec 64} (e₁ : s₁.gpr .r15 = x) (e₂ : s₂.gpr .r15 = x) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r6, .r15, .r19, .r30, .r31], s₁.gpr r = s₂.gpr r := by
  refine ⟨p₁.trans p₂.symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.vc.ctx.r6, h₂.vc.ctx.r6]
  · rw [e₁, e₂]
  · rw [h₁.r19, h₂.r19]
  · rw [h₁.vc.r30, h₂.vc.r30]
  · rw [h₁.vc.r31, h₂.vc.r31]

/-- `wregs`, with the digit in `a2`. -/
theorem wregs2 {s₁ s₂ : State} (h₁ : WCtx b pk sig ch T A K S s₁) (h₂ : WCtx b pk sig ch T A K S s₂)
    (p₁ : s₁.sp = sp) (p₂ : s₂.sp = sp) {x y : BitVec 64} (e₁ : s₁.gpr .r15 = x) (e₂ : s₂.gpr .r15 = x)
    (a₁ : s₁.gpr .r9 = y) (a₂ : s₂.gpr .r9 = y) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r9, .r6, .r15, .r19, .r30, .r31], s₁.gpr r = s₂.gpr r := by
  refine ⟨p₁.trans p₂.symm, fun r hr => ?_⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [a₁, a₂]
  · exact (wregs h₁ h₂ p₁ p₂ e₁ e₂).2 r hr

/-- Within window `c`, the sum representing `v`. -/
def WM (b sp pk sig ch T : Addr) (A : Spec.Ed25519.Point) (K S c : Nat) (v : EPoint dZ) (t : State) : Prop :=
  WCtx b pk sig ch T A K S t ∧ t.sp = sp ∧ env t.mem b 16 = Spec.Ed25519.d ∧
    t.gpr .r15 = BitVec.ofNat 64 c ∧ Rep (point (env t.mem b) 0 1 2 3) v

/-- `WM`, with digit `dg` in `a2`. -/
def WD (b sp pk sig ch T : Addr) (A : Spec.Ed25519.Point) (K S c : Nat) (v : EPoint dZ) (dg : Nat)
    (t : State) : Prop :=
  WM b sp pk sig ch T A K S c v t ∧ t.gpr .r9 = BitVec.ofNat 64 dg

theorem WD.regs {c dg : Nat} {v : EPoint dZ} {s₁ s₂ : State} (h₁ : WD b sp pk sig ch T A K S c v dg s₁)
    (h₂ : WD b sp pk sig ch T A K S c v dg s₂) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r9, .r6, .r15, .r19, .r30, .r31], s₁.gpr r = s₂.gpr r :=
  wregs2 h₁.1.1 h₂.1.1 h₁.1.2.1 h₂.1.2.1 h₁.1.2.2.2.1 h₂.1.2.2.2.1 h₁.2 h₂.2

theorem WM.regs {c : Nat} {v v' : EPoint dZ} {s₁ s₂ : State} (h₁ : WM b sp pk sig ch T A K S c v s₁)
    (h₂ : WM b sp pk sig ch T A K S c v' s₂) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r6, .r15, .r19, .r30, .r31], s₁.gpr r = s₂.gpr r :=
  wregs h₁.1 h₂.1 h₁.2.1 h₂.2.1 h₁.2.2.2.1 h₂.2.2.2.1

theorem addA_ct {c dg : Nat} (hdg : dg < 16) {v : EPoint dZ} :
    RelCT isa (Both (WD b sp pk sig ch T A K S c v dg)) addA fun _ _ => True := by
  unfold addA
  refine ct_ite (decide (dg ≠ 0)) (fun s h => eval_nz_ofNat s .r9 (by omega) h.2) (fun _ => ?_) (fun _ => ?_)
  · exact ctRegs [.r9, .r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)
  · exact ctRegs [.r9, .r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)

theorem addB_ct {c dg : Nat} (hdg : dg < 16) {v : EPoint dZ} :
    RelCT isa (Both (WD b sp pk sig ch T A K S c v dg)) addB fun _ _ => True := by
  unfold addB
  refine ct_ite (decide (dg ≠ 0)) (fun s h => eval_nz_ofNat s .r9 (by omega) h.2) (fun _ => ?_) (fun _ => ?_)
  · exact ctRegs [.r9, .r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)
  · exact ctRegs [.r9, .r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)

/-- `WM` through a `Rest` that keeps the pointers and `r15`, a frame of `FA`, and slots 0–3 and 16. -/
theorem WM.of {c : Nat} {v : EPoint dZ} {s t : State} {R : List Reg} (h : WM b sp pk sig ch T A K S c v s)
    (hr : Rest R s t) (hR : ∀ r ∈ [Reg.r6, .r29, .r30, .r31], r ∉ R) (h5 : Reg.r19 ∉ R) (h1 : Reg.r15 ∉ R)
    (hf : Frame [FA b] s.mem t.mem) {v' : EPoint dZ} (hp : Rep (point (env t.mem b) 0 1 2 3) v')
    (hd : env t.mem b 16 = env s.mem b 16) : WM b sp pk sig ch T A K S c v' t :=
  ⟨h.1.of hr hR h5 hf, by rw [hr.sp, h.2.1], by rw [hd, h.2.2.1], by rw [hr.gpr _ h1, h.2.2.2.1], hp⟩

theorem windowB_ct {c : Nat} (hc : c < 128) {v : EPoint dZ} :
    RelCT isa (Both (WM b sp pk sig ch T A K S c v)) windowB fun _ _ => True := by
  unfold windowB
  refine ct_seq (B := fun t => WM b sp pk sig ch T A K S c v t ∧ (t.gpr .r7 == 0) = decide (c < 64))
    (ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide))
    (fun s h => wp_lsr (by decide) fun t u2 => WP.block_nil ⟨?_, ?_⟩) ?_
  · have r2 : Rest [.r7] s t := u2.rest (by decide)
    exact h.of r2 (by decide) (by decide) (by decide) (by rw [u2.mem]; exact Frame.refl _ _)
      (by rw [u2.mem]; exact h.2.2.2.2) (by rw [u2.mem])
  · rw [u2.gpr, h.2.2.2.1]; exact lsr6_fact c hc
  refine ct_ite (decide (c < 64)) (fun s h => by rw [eval_zero, h.2]) (fun hb => ?_) (fun _ => ?_)
  swap
  · exact ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide)
  have hc64 : c < 64 := of_decide_eq_true hb
  refine ct_seq (B := WD b sp pk sig ch T A K S c v (S / 16 ^ c % 16))
    (ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
    (fun s h => WP.mono (digitS_ok h.1.1 hc64 h.1.2.2.2.1) fun t ⟨rt, mt, et⟩ =>
      ⟨h.1.of rt (by decide) (by decide) (by decide) (by rw [mt]; exact Frame.refl _ _)
        (by rw [mt]; exact h.1.2.2.2.2) (by rw [mt]), et⟩) (addB_ct (Nat.mod_lt _ (by decide)))

/-- The windows' invariant in each run, with `n` windows left. -/
def WinCT (b sp pk sig ch T : Addr) (A : Spec.Ed25519.Point) (K S : Nat) (Aa : EPoint dZ) (n : Nat)
    (t : State) : Prop :=
  1 ≤ n ∧ n ≤ 128 ∧ WCtx b pk sig ch T A K S t ∧ t.sp = sp ∧ env t.mem b 16 = Spec.Ed25519.d ∧
    t.gpr .r15 = BitVec.ofNat 64 n ∧
    RepP (point (env t.mem b) 0 1 2 3) ((K / 16 ^ n) • Aa + (S / 16 ^ n) • (-baseAff))

theorem windowStep_ct {Aa : EPoint dZ} (hA : Rep A Aa) {c : Nat} (hc : c < 128) :
    RelCT isa (Both (WinCT b sp pk sig ch T A K S Aa (c + 1))) windowStep fun _ _ => True := by
  have hS : ∀ t, WCtx b pk sig ch T A K S t → S < 256 ^ 32 := fun t h => h.sc ▸ Proof.Ed25519.decodeLE_lt32 _ _
  let v1 := (K / 16 ^ (c + 1)) • Aa + (S / 16 ^ (c + 1)) • (-baseAff)
  let M1 (t : State) : Prop := WCtx b pk sig ch T A K S t ∧ t.sp = sp ∧ env t.mem b 16 = Spec.Ed25519.d ∧
    t.gpr .r15 = BitVec.ofNat 64 c ∧ RepP (point (env t.mem b) 0 1 2 3) v1
  unfold windowStep
  refine ct_seq (B := M1)
    (ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ =>
      wregs h₁.2.2.1 h₂.2.2.1 h₁.2.2.2.1 h₂.2.2.2.1 h₁.2.2.2.2.2.1 h₂.2.2.2.2.2.1) (by taint_decide))
    (fun s h => wp_subi (imm := 1) (by decide) (by decide) fun t u => WP.block_nil ?_) ?_
  · obtain ⟨_, _, hw, hsp, hd, h1, hv⟩ := h
    have r1 : Rest [.r15] s t := u.rest (by decide)
    refine ⟨hw.of r1 (by decide) (by decide) (by rw [u.mem]; exact Frame.refl _ _), by rw [r1.sp, hsp],
      by rw [u.mem, hd], ?_, by rw [u.mem]; exact hv⟩
    rw [u.gpr, h1, BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ _
  refine ct_seq (B := WM b sp pk sig ch T A K S c ((16 : Nat) • v1))
    (ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ =>
      wregs h₁.1 h₂.1 h₁.2.1 h₂.2.1 h₁.2.2.2.1 h₂.2.2.2.1) (by taint_decide))
    (fun s h => WP.mono (dbl4_ok h.1.vc.ctx) fun t ⟨k, f, e, e16⟩ =>
      ⟨h.1.of k (by decide) (by decide) f, by rw [k.sp, h.2.1], by rw [e16, h.2.2.1],
        by rw [k.gpr _ (by decide), h.2.2.2.1], by rw [e]; exact dbl4_rep h.2.2.2.2⟩) ?_
  refine ct_seq (B := WD b sp pk sig ch T A K S c ((16 : Nat) • v1) (K / 16 ^ c % 16))
    (ctRegs [.r6, .r15, .r19, .r30, .r31] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide))
    (fun s h => WP.mono (digitK_ok h.1 hc h.2.2.2.1) fun t ⟨rt, mt, et⟩ =>
      ⟨h.of rt (by decide) (by decide) (by decide) (by rw [mt]; exact Frame.refl _ _)
        (by rw [mt]; exact h.2.2.2.2) (by rw [mt]), et⟩) ?_
  refine ct_seq (B := WM b sp pk sig ch T A K S c ((16 : Nat) • v1 + (K / 16 ^ c % 16) • Aa))
    (addA_ct (Nat.mod_lt _ (by decide)))
    (fun s h => WP.mono (addA_ok h.1.1 hA (Nat.mod_lt _ (by decide)) h.2 h.1.2.2.2.2) fun t ⟨rt, ft, pt, dt⟩ =>
      h.1.of rt (by decide) (by decide) (by decide) ft pt dt) (windowB_ct hc)

/-- **The windows**, from `W` left. -/
theorem windows_ct {Aa : EPoint dZ} (hA : Rep A Aa) (W : Nat) :
    RelCT isa (Both (WinCT b sp pk sig ch T A K S Aa W)) windows fun _ _ => True := by
  unfold windows
  refine RelCT.loop (M := isa) (fun n => Both (WinCT b sp pk sig ch T A K S Aa n)) (fun n => ?_) W
  rcases n with _ | c
  · exact RelCT.of_false fun _ _ h => absurd h.1.1 (by omega)
  by_cases hc : c < 128
  · refine (ctBoth (windowStep_ct hA hc) (B := WM b sp pk sig ch T A K S c
        ((K / 16 ^ c) • Aa + (S / 16 ^ c) • (-baseAff))) fun s h => WP.mono
        (windowStep_ok h.2.2.1 h.2.2.2.2.1 hA (h.2.2.1.sc ▸ Proof.Ed25519.decodeLE_lt32 _ _) hc h.2.2.2.2.2.1
          h.2.2.2.2.2.2) fun t ⟨ht, dt, et, vt, rt, _⟩ => ⟨ht, by rw [rt.sp, h.2.2.2.1], dt, et, vt⟩).mono
      (fun _ _ h => h) fun s₁ s₂ h => ⟨?_, fun _ => trivial, fun he => ⟨c, by omega, ?_⟩⟩
    · rw [eval_nz_ofNat s₁ .r15 (by omega) h.1.2.2.2.1, eval_nz_ofNat s₂ .r15 (by omega) h.2.2.2.2.1]
    · rw [eval_nz_ofNat s₁ .r15 (by omega) h.1.2.2.2.1] at he
      have hc0 : c ≠ 0 := by simpa using he
      exact ⟨⟨by omega, by omega, h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, rep_repP h.1.2.2.2.2⟩,
        ⟨by omega, by omega, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, rep_repP h.2.2.2.2.2⟩⟩
  · exact RelCT.of_false fun _ _ h => absurd h.1.2.1 (by omega)

end

/-! ## `verifyRhs` -/

/-- **`verifyRhs` leaks only its inputs.** -/
theorem rhs_ct : RhsCT := by
  intro b sp pk sig ch T PK RS CH SS a r ha hr
  obtain ⟨Aa, hA⟩ := Proof.Ed25519.decodePoint_rep ha
  obtain ⟨Ra, hR⟩ := Proof.Ed25519.decodePoint_rep hr
  have dR : ∀ r' ∈ [FA b, (⟨b + BitVec.ofNat 64 TA, 1920⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 7904, 128⟩ r' := fun r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    · exact Offset.disjoint _ (.inr (by rw [TA_eq]; omega)) (by omega) (by rw [TA_eq]; omega)
  have dR1 : ∀ r' ∈ [FA b], Region.Disjoint ⟨b + BitVec.ofNat 64 7904, 128⟩ r' := fun r' hr' =>
    dR r' (by simp only [List.mem_singleton] at hr'; simp [hr'])
  have sigD : ∀ {t : State}, VCtx b pk sig ch t →
      (⟨sig + BitVec.ofNat 64 32, 32⟩ : Region).Disjoint ⟨b, 8192⟩ := fun h =>
    h.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide))
  unfold verifyRhs
  -- `A` into slots 0–3.
  let R1 (t : State) : Prop := VCtx b pk sig ch t ∧ t.sp = sp ∧ BStat b T t ∧ t.syms bSym = T ∧
    point (env t.mem b) 0 1 2 3 = a ∧ tableAt t.mem b 7904 = r ∧ bytesAt t.mem ch 64 = CH ∧
    bytesAt t.mem (sig + BitVec.ofNat 64 32) 32 = SS
  have c1 := ctBoth (ctRegs [.r6] (A := RhsPre b sp pk sig ch T a r CH SS) (c := .block (pointTableRead 7776))
    (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, fun x hx => by
      rw [List.mem_singleton.mp hx, h₁.1.ctx.r6, h₂.1.ctx.r6]⟩) (by taint_decide)) (B := R1) fun s h =>
    WP.mono_syms (rhsRead_ok h.1.ctx) fun t ⟨rt, ft, pt⟩ sy =>
      ⟨h.1.of_rest rt (by decide), by rw [rt.sp, h.2.1], h.2.2.1.of_frame rt.rd ft fa_sub,
        by rw [sy]; exact h.2.2.2.1, by rw [pt, h.2.2.2.2.1], by rw [tableAt_keep ft dR1, h.2.2.2.2.2.1],
        by rw [bytesAt_ws ft fa_sub h.1.chD (by decide), h.2.2.2.2.2.2.1],
        by rw [bytesAt_ws ft fa_sub (sigD h.1) (by decide), h.2.2.2.2.2.2.2]⟩
  -- The preparation.
  let R2 (t : State) : Prop := WCtx b pk sig ch T a (decodeLE CH) (decodeLE SS) t ∧ t.sp = sp ∧
    env t.mem b 16 = Spec.Ed25519.d ∧ point (env t.mem b) 0 1 2 3 = Spec.Ed25519.identity ∧
    tableAt t.mem b 7904 = r ∧ bytesAt t.mem ch 64 = CH
  have c2 := ctBoth (RelCT.taint (A := taintSym [bSym]) (Taint.ofRegs [.r6]) (P := Both R1) (c := strausPrep)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨⟨h₁.2.1.trans h₂.2.1.symm, fun x hx => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hx
      subst hx; rw [h₁.1.ctx.r6, h₂.1.ctx.r6]⟩, fun n hn => by
        rw [List.mem_singleton.mp hn, h₁.2.2.2.1, h₂.2.2.2.1]⟩) (by taint_decide)) (B := R2) fun s h =>
    WP.mono (strausPrep_ok h.1 h.2.2.1 h.2.2.2.1) fun t ⟨wt, dt, it, rt, ft⟩ => by
      rw [h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2] at wt
      exact ⟨wt, by rw [rt.sp, h.2.1], dt, it, by rw [tableAt_keep ft dR, h.2.2.2.2.2.1],
        by rw [bytesAt_ws ft prepW_sub h.1.chD (by decide), h.2.2.2.2.2.2.1]⟩
  -- The count.
  let R3 (W : Nat) (t : State) : Prop := (W = 64 ∨ W = 128) ∧
    (W = 64 ↔ ∀ i < 32, CH.getD (32 + i) 0 = 0) ∧
    WinCT b sp pk sig ch T a (decodeLE CH) (decodeLE SS) Aa W t ∧ tableAt t.mem b 7904 = r
  have c3 : RelCT isa (Both R2) windowCount fun s₁ s₂ => ∃ W, Both (R3 W) s₁ s₂ := by
    unfold windowCount
    have hch := RelCT.seq (ctBoth (ctRegs [.r6, .r31] (A := R2) (c := .block challengeHigh)
      (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · rw [h₁.1.vc.ctx.r6, h₂.1.vc.ctx.r6]
        · rw [h₁.1.vc.r31, h₂.1.vc.r31]⟩) (by taint_decide))
      (B := fun t => R2 t ∧ (t.gpr .r8 = 0 ↔ ∀ i < 32, CH.getD (32 + i) 0 = 0)) fun s h =>
        WP.mono (challengeHigh_ok h.1.vc.r31 fun i hi => in_base (List.mem_append_left _ h.1.vc.chR)
          (by omega) (by omega)) fun t ⟨rt, mt, et⟩ => ⟨by
            refine ⟨h.1.of rt (by decide) (by decide) (by rw [mt]; exact Frame.refl _ _), by rw [rt.sp, h.2.1],
              by rw [mt]; exact h.2.2.1, by rw [mt]; exact h.2.2.2.1, by rw [mt]; exact h.2.2.2.2.1,
              by rw [mt]; exact h.2.2.2.2.2⟩, by
            rw [et, ← h.2.2.2.2.2]
            exact forall_congr' fun i => imp_congr_right fun hi => by rw [bytesAt_getD _ _ (by omega)]⟩)
      (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2)
        ((ctRegs [] (A := R2) (c := .block [.li .r15 64]) (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, by simp⟩)
          (by taint_decide)).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
        ((ctRegs [] (A := R2) (c := .block [.li .r15 128]) (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, by simp⟩)
          (by taint_decide)).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h))
    refine (ctBoth hch (B := fun t => ∃ W, R3 W t) fun s h => WP.mono (windowCount_ok h.1.vc)
      fun t ⟨rt, mt, W, hW, hW64, et, hK⟩ => ⟨W, hW, ?_, ⟨by omega, by omega,
        h.1.of rt (by decide) (by decide) (by rw [mt]; exact Frame.refl _ _), by rw [rt.sp, h.2.1],
        by rw [mt]; exact h.2.2.1, et, ?_⟩, by rw [mt]; exact h.2.2.2.2.1⟩).mono (fun _ _ h => h) ?_
    · rw [hW64, ← h.2.2.2.2.2]
      exact forall_congr' fun i => imp_congr_right fun hi => by rw [bytesAt_getD _ _ (by omega)]
    · have hS : decodeLE SS < 256 ^ 32 := h.1.sc ▸ Proof.Ed25519.decodeLE_lt32 _ _
      rw [h.2.2.2.2.2] at hK
      rw [Nat.div_eq_of_lt hK, Proof.Ed25519.nibble_high_zero hS (by omega), zero_nsmul, zero_nsmul, add_zero,
        mt, h.2.2.2.1]
      exact rep_repP Proof.Ed25519.identity_rep
    · rintro s₁ s₂ ⟨⟨W₁, h₁⟩, ⟨W₂, h₂⟩⟩
      have e : W₁ = W₂ := by
        rcases h₁.1 with rfl | rfl <;> rcases h₂.1 with rfl | rfl
        · rfl
        · exact absurd (h₂.2.1.mpr (h₁.2.1.mp rfl)) (by decide)
        · exact absurd (h₁.2.1.mpr (h₂.2.1.mp rfl)) (by decide)
        · rfl
      subst e
      exact ⟨W₁, h₁, h₂⟩
  -- The windows, `-R` and the comparison.
  have tail : ∀ W, RelCT isa (Both (R3 W)) (.seq windows (.seq negR Impl.Ed25519.PPC64LE.pointEqual))
      fun _ _ => True := fun W => by
    let R4 (t : State) : Prop := Ctx8 b t ∧ t.sp = sp ∧
      Rep (point (env t.mem b) 0 1 2 3) (decodeLE CH • Aa + decodeLE SS • (-baseAff)) ∧
      tableAt t.mem b 7904 = r
    have c4 := ctBoth (A := R3 W) ((windows_ct (b := b) (sp := sp) (pk := pk) (sig := sig) (ch := ch) (T := T) (A := a)
      (K := decodeLE CH) (S := decodeLE SS) hA W).mono (fun _ _ h => ⟨h.1.2.2.1, h.2.2.2.1⟩) fun _ _ h => h)
      (B := R4) fun s h => WP.mono (windows_ok h.2.2.1.1 h.2.2.1.2.1 h.2.2.1.2.2.1 h.2.2.1.2.2.2.2.1 hA
        (h.2.2.1.2.2.1.sc ▸ Proof.Ed25519.decodeLE_lt32 _ _) h.2.2.1.2.2.2.2.2.1 h.2.2.1.2.2.2.2.2.2)
        fun t ⟨wt, rt, ft, vt⟩ => ⟨wt.vc.ctx, by rw [rt.sp, h.2.2.1.2.2.2.1], vt,
          by rw [tableAt_keep ft dR1, h.2.2.2]⟩
    have c5 := ctBoth (ctRegs [.r6] (A := R4) (c := negR) (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm,
      fun x hx => by rw [List.mem_singleton.mp hx, h₁.1.r6, h₂.1.r6]⟩) (by taint_decide))
      (B := EqRepPre b sp (decodeLE CH • Aa + decodeLE SS • (-baseAff)) (-Ra)) fun s h =>
        WP.mono (negR_ok h.1) fun t ⟨rt, _, ct, qt, pt⟩ =>
          ⟨⟨ct, by rw [rt.sp, h.2.1]⟩, by rw [pt]; exact rep_repP h.2.2.1,
            by rw [qt, h.2.2.2]; exact rep_repP hR.neg⟩
    exact RelCT.seq c4 (RelCT.seq c5 (pointEqualRep_ct _ _))
  refine RelCT.seq c1 (RelCT.seq c2 (RelCT.seq c3 ?_))
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨W, hW⟩ e₁ e₂ => tail W s₁ s₂ t₁ t₂ s₁' s₂' hW e₁ e₂

end VG.Proof.Ed25519.PPC64LE
