module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Sha512OK
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Sha512OK
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
public import VerifiedGarbage.Impl.Ed25519.RISCV64.VerifyWindow
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
import VerifiedGarbage.Proof.Ed25519.Challenge
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyFn
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Verify
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
meta import VerifiedGarbage.Impl.Ed25519.RISCV64.VerifyWindow
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
meta import VerifiedGarbage.Proof.Ed25519.Challenge
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyFn
meta import VerifiedGarbage.Impl.Ed25519.RISCV64.Verify
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
meta import VerifiedGarbage.Proof.X25519.RISCV64.Instr
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Proof.X25519.RISCV64.Invert

/-! ### `Ed25519.RISCV64.VerifyCT`, which this module and modules that import it used -/

section

/-! ### `Ed25519.RISCV64.DecodeCT`, which only this module used -/

section

/-!
# Ed25519 on RISC-V: a decoding leaks only its encoding

Two runs of `pointDecode` on the same encoding, with the same working space
and stack pointer, leak the same trace (`pointDecode_ct`). The taint analysis
(`taint_decide`) checks each piece between the branches: memory is secret to
it, so the branches on `a2` are related by correctness instead: in both runs
`a2` is zero exactly when the same fact about the encoding holds (`RelCT.ite`).
Each relation says that both runs satisfy the same predicate of public values
(`Both`), as ARMv7's proofs do.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P Fe)
open VG.Spec.Ed25519 (decodeLE bytesAt)
open VG.Proof.Ed25519 (rootU rootV rootX)

/-- Both runs satisfy `A`. -/
abbrev Both (A : State → Prop) (s₁ s₂ : State) : Prop := A s₁ ∧ A s₂

theorem ctBoth {A B : State → Prop} {c : Prog isa} (h : RelCT isa (Both A) c fun _ _ => True)
    (hw : ∀ s, A s → WP isa c s B) : RelCT isa (Both A) c (Both B) :=
  (h.wp (F₁ := B) (F₂ := B) fun _ _ hp => ⟨hw _ hp.1, hw _ hp.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Code the taint analysis checks, with the registers of `rs` and `sp` agreeing. -/
theorem ctRegs (rs : List Reg) {A : State → Prop} {c : Prog isa}
    (hr : ∀ s₁ s₂, A s₁ → A s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {hc : Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa (Both A) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ hp => ⟨(hr _ _ hp.1 hp.2).1, fun r h => (hr _ _ hp.1 hp.2).2 r (by simpa using h)⟩) h

theorem eval_zero_agree {s₁ s₂ : State} {r : Reg} {p : Prop} (h₁ : s₁.gpr r = 0 ↔ p) (h₂ : s₂.gpr r = 0 ↔ p) :
    isa.eval (.zero r) s₁ = isa.eval (.zero r) s₂ := by
  rw [eval_zero, eval_zero]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact h₁.trans h₂.symm

/-- The working space at `a3` and the stack pointer. -/
def Pin (b sp : Addr) (s : State) : Prop := Ctx8 b s ∧ s.sp = sp

theorem Pin.regs {b sp : Addr} {s₁ s₂ : State} (h₁ : Pin b sp s₁) (h₂ : Pin b sp s₂) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a3], s₁.gpr r = s₂.gpr r :=
  ⟨h₁.2.trans h₂.2.symm, fun r hr => by rw [List.mem_singleton.mp hr, h₁.1.a3, h₂.1.a3]⟩

theorem Pin.of_rest {b sp : Addr} {s t : State} {R : List Reg} (h : Pin b sp s) (hr : Rest R s t)
    (h6 : Reg.a3 ∉ R) : Pin b sp t :=
  ⟨h.1.of_rest hr h6, by rw [hr.sp, h.2]⟩

section
variable {b sp : Addr}

theorem recoverInvalid_ct : RelCT isa (Both (Pin b sp)) recoverInvalid fun _ _ => True :=
  ctRegs [.a3] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)

/-- Before the sign is applied: `x` in slot 0, the sign at `SIGN`. -/
def AdjPre (b sp : Addr) (x : Fe) (sg : Bool) (s : State) : Prop :=
  Pin b sp s ∧ env s.mem b 0 = x ∧ SignAt b sg s.mem

theorem recoverAdjust_ct (x : Fe) (sg : Bool) :
    RelCT isa (Both (AdjPre b sp x sg)) recoverAdjustSign fun _ _ => True := by
  unfold recoverAdjustSign
  have h1 := ctBoth (ctRegs [.a3] (A := AdjPre b sp x sg) (c := .block (freeze 0 ++ recoverParity))
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
    (B := fun t => Pin b sp t ∧ (t.gpr .a2 = 0 ↔ ((x.val % 2 == 1) == sg) = true)) fun s h =>
      WP.mono (adjParity_ok h.1.1 h.2.2) fun t ⟨k, _, e⟩ => ⟨h.1.of_rest k.rest (by decide), by rw [← h.2.1]; exact e⟩
  refine RelCT.seq h1 (RelCT.seq (Q := fun _ _ => True) (R := Both (Pin b sp))
    (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_) ?_)
  · exact RelCT.block_nil fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩
  · exact (ctBoth (ctRegs [.a3] (A := Pin b sp) (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide))
      fun s h => WP.mono (fieldCode_ok _ h.1.ctx h.1.ws) fun t ⟨k, _⟩ => h.of_rest k.rest (by decide)).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact ctRegs [.a3] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)

theorem recoverSign_ct (x : Fe) (sg : Bool) :
    RelCT isa (Both (AdjPre b sp x sg)) recoverSign fun _ _ => True := by
  unfold recoverSign
  have h1 := ctBoth (ctRegs [.a3] (A := AdjPre b sp x sg) (c := fieldZero 0)
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
    (B := fun t => AdjPre b sp x sg t ∧ (t.gpr .a2 = 0 ↔ x = 0)) fun s h =>
      WP.mono (fieldZero_ok h.1.1.ctx 0) fun t ⟨r, f, e⟩ =>
        ⟨⟨h.1.of_rest r (by decide), by rw [env_FR f, h.2.1], h.2.2.frame (frame_FR f)⟩,
          by rw [e, ← h.2.1, Fin.ext_iff]; exact Iff.rfl⟩
  refine RelCT.seq h1 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · unfold signTest
    have h2 := ctBoth (ctRegs [.a3] (A := AdjPre b sp x sg) (c := .block [.load .w .a2 .a3 SIGN])
      (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
      (B := fun t => AdjPre b sp x sg t ∧ t.gpr .a2 = BitVec.ofNat 64 sg.toNat) fun s h =>
        lw0_ok h.1.1.ctx (d := SIGN) (by decide) (by decide) fun t u => WP.block_nil
            ⟨⟨h.1.of_rest (u.rest (ws := [.a2]) (by decide)) (by decide), by rw [u.mem]; exact h.2.1,
              by rw [u.mem]; exact h.2.2⟩, by rw [u.gpr]; exact h.2.2⟩
    refine RelCT.seq (h2.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
      (RelCT.ite (fun _ _ h => by rw [eval_nonzero, eval_nonzero, h.1.2, h.2.2]) ?_ ?_)
    · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h
    · exact (recoverAdjust_ct x sg).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact (recoverAdjust_ct x sg).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h

/-- Before the candidate: `y` in slot 1, the sign at `SIGN`. -/
def RPPre (b sp : Addr) (y : Fe) (sg : Bool) (s : State) : Prop :=
  Pin b sp s ∧ env s.mem b 1 = y ∧ SignAt b sg s.mem

theorem recoverPoint_ct (y : Fe) (sg : Bool) :
    RelCT isa (Both (RPPre b sp y sg)) recoverPoint fun _ _ => True := by
  unfold recoverPoint
  -- The candidate, and `v x²` against `u` and `-u`.
  let C (t : State) : Prop := Pin b sp t ∧ SignAt b sg t.mem ∧ env t.mem b 0 = rootX y ∧
    env t.mem b 11 = rootV y * rootX y * rootX y ∧ env t.mem b 6 = rootU y ∧ env t.mem b 12 = 0 - rootU y
  have h1 := ctBoth (ctRegs [.a3] (A := RPPre b sp y sg) (c := recoverCandidate)
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide)) (B := C) fun s h =>
      WP.mono (recoverCandidate_ok h.1.1) fun t ⟨k, x0, _, x6, _, x11, x12⟩ =>
        ⟨h.1.of_rest k.rest (by decide), h.2.2.frame k.frame, by rw [x0, h.2.1], by rw [x11, h.2.1],
          by rw [x6, h.2.1], by rw [x12, h.2.1]⟩
  have hC (t : State) (h : C t) {u : State} (k : Keep b t u) {c : Slot}
      (e : env u.mem b = evalOps [.sub 21 11 c] (env t.mem b)) : C u :=
    ⟨h.1.of_rest k.rest (by decide), h.2.1.frame k.frame, by rw [e]; exact h.2.2.1, by rw [e]; exact h.2.2.2.1,
      by rw [e]; exact h.2.2.2.2.1, by rw [e]; exact h.2.2.2.2.2⟩
  have h6 := ctBoth (ctRegs [.a3] (A := C) (c := fieldEqual 11 6) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => C t ∧ (t.gpr .a2 = 0 ↔ rootV y * rootX y * rootX y = rootU y)) fun s h =>
      WP.mono (fieldEqual_ok h.1.1.ctx h.1.1.ws 11 6) fun t ⟨k, e, z⟩ =>
        ⟨hC s h k e, by rw [z, h.2.2.2.1, h.2.2.2.2.1]⟩
  have h12 := ctBoth (ctRegs [.a3] (A := C) (c := fieldEqual 11 12) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => C t ∧ (t.gpr .a2 = 0 ↔ rootV y * rootX y * rootX y = 0 - rootU y))
      fun s h => WP.mono (fieldEqual_ok h.1.1.ctx h.1.1.ws 11 12) fun t ⟨k, e, z⟩ =>
        ⟨hC s h k e, by rw [z, h.2.2.2.1, h.2.2.2.2.2]⟩
  have hA (t : State) (h : C t) : AdjPre b sp (rootX y) sg t := ⟨h.1, h.2.2.1, h.2.1⟩
  refine RelCT.seq h1 (RelCT.seq h6 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_))
  · exact (recoverSign_ct (rootX y) sg).mono (fun _ _ h => ⟨hA _ h.1.1.1, hA _ h.1.2.1⟩) fun _ _ h => h
  refine RelCT.seq (h12.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
    (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · have hF := ctBoth (ctRegs [.a3] (A := C) (c := fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18])
      (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
      (B := AdjPre b sp (rootX y * Spec.Ed25519.sqrtM1) sg) fun s h =>
        WP.mono (fieldCode_ok _ h.1.1.ctx h.1.1.ws) fun t ⟨k, e⟩ =>
          ⟨h.1.of_rest k.rest (by decide), by rw [e, ← h.2.2.1]; rfl, h.2.1.frame k.frame⟩
    exact RelCT.seq (hF.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h) (recoverSign_ct _ sg)
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h

/-- Before a decoding: the encoding `bs` at `s0`. -/
def DecPre (b sp q : Addr) (bs : List Byte) (s : State) : Prop :=
  Pin b sp s ∧ s.gpr .s0 = q ∧ (∀ k < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (0 + 4 * k)) 4) ∧
    (⟨q + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 (offset 1), 32⟩ ∧ bytesAt s.mem q 32 = bs

/-- **A decoding leaks only its encoding.** -/
theorem pointDecode_ct (q : Addr) (bs : List Byte) :
    RelCT isa (Both (DecPre b sp q bs)) pointDecode fun _ _ => True := by
  unfold pointDecode
  have h1 := ctBoth (ctRegs [.a3, .s0] (A := DecPre b sp q bs) (c := pointDecodeLoad)
    (fun _ _ h₁ h₂ => ⟨h₁.1.2.trans h₂.1.2.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.a3, h₂.1.1.a3]
      · rw [h₁.2.1, h₂.2.1]⟩) (by taint_decide))
    (B := fun t => RPPre b sp (Proof.X25519.toFe (decodeLE bs % 2 ^ 255)) (decodeLE bs / 2 ^ 255 == 1) t ∧
      (t.gpr .a2 = 0 ↔ decodeLE bs % 2 ^ 255 < P)) fun s h =>
      WP.mono (pointDecodeLoad_ok h.1.1 h.2.1 h.2.2.1 h.2.2.2.1) fun t ⟨k, sg, y, z⟩ => by
        rw [h.2.2.2.2] at sg y z
        exact ⟨⟨h.1.of_rest k.rest (by decide), y, sg⟩, z⟩
  refine RelCT.seq h1 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · exact (recoverPoint_ct _ _).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h

end

end VG.Proof.Ed25519.RISCV64

end

end

/-!
# `vg_ed25519_verify_equation` on RISC-V leaks only its inputs

Two runs with the same pointers, stack pointer and input bytes leak the same
trace (`verify_ct`). As for a decoding (`DecodeCT.lean`), the taint analysis
checks the code between the branches, and each branch on a value loaded from
memory (`S < L`, both points decoded, the comparison) is related by
correctness: both runs take it on the same fact about the inputs.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P Fe)
open VG.Spec.Ed25519 (decodeLE bytesAt)

/-! ## The decoding loop -/

section
variable {b sp pk sig ch : Addr} {PK RS : List Byte}

/-- After `k` decodings, from inputs whose encodings are `PK` and `RS`. -/
def DecCT (b sp pk sig ch : Addr) (PK RS : List Byte) (k : Nat) (s : State) : Prop :=
  ∃ s0, DecInv s0 b pk sig ch k s ∧ s.sp = sp ∧ bytesAt s0.mem pk 32 = PK ∧ bytesAt s0.mem sig 32 = RS

def inBytes (PK RS : List Byte) (k : Nat) : List Byte := if k = 0 then PK else RS

theorem decodeBody_ct {k : Nat} :
    RelCT isa (Both (DecCT b sp pk sig ch PK RS k)) decodeBody fun _ _ => True := by
  unfold decodeBody
  let B1 (t : State) : Prop := DecPre b sp (inPtr pk sig k) (inBytes PK RS k) t ∧
    t.gpr .s8 = BitVec.ofNat 64 (7776 + 128 * k) ∧ t.gpr .s10 = sig
  have h1 := ctBoth (ctRegs [.a3, .s7] (A := DecCT b sp pk sig ch PK RS k) (c := .block [.addi .s0 .s7 0])
    (fun _ _ ⟨_, d₁, p₁, _⟩ ⟨_, d₂, p₂, _⟩ => ⟨p₁.trans p₂.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [d₁.ctx.ctx.a3, d₂.ctx.ctx.a3]
      · rw [d₁.s7, d₂.s7]⟩) (by taint_decide)) (B := B1) fun s ⟨s0, d, hsp, hpk, hrs⟩ => by
    have h1 : offset 1 = 96 := rfl
    refine wp_mv fun t1 u1 => WP.block_nil ?_
    have hv1 : VCtx b pk sig ch t1 := d.ctx.of_rest (u1.rest (ws := [.s0]) (by decide)) (by decide)
    have hq : (∀ j < 8, InRegions (t1.rd ++ t1.wr) (inPtr pk sig k + BitVec.ofNat 64 (0 + 4 * j)) 4) ∧
        (⟨inPtr pk sig k, 32⟩ : Region).Disjoint ⟨b, 8192⟩ ∧ bytesAt s0.mem (inPtr pk sig k) 32 = inBytes PK RS k := by
      unfold inPtr inBytes
      by_cases h0 : k = 0
      · rw [iteT h0, iteT h0]
        exact ⟨fun j hj => in_base (List.mem_append_left _ hv1.pkR) (by omega_using [hj]) (by omega_using [hj]), hv1.pkD, hpk⟩
      · rw [iteF h0, iteF h0]
        exact ⟨fun j hj => in_base (List.mem_append_left _ hv1.sigR) (by omega_using [hj]) (by omega_using [hj]),
          hv1.sigD.sub_left (Region.sub_prefix (by decide)), hrs⟩
    obtain ⟨hr4, hdq, hbs⟩ := hq
    refine ⟨⟨⟨hv1.ctx, by rw [u1.sp, hsp]⟩, by rw [u1.gpr, d.s7], hr4, by
      rw [BitVec.add_zero]; exact hdq.sub_right (Offset.sub_base b (by omega)), ?_⟩,
      by rw [u1.other _ (by decide), d.s8], by rw [u1.other _ (by decide), d.ctx.s10]⟩
    rw [u1.mem, bytesAt_ws d.frame decW_sub hdq (by decide), hbs]
  let B2 (t : State) : Prop := Pin b sp t ∧ t.gpr .s8 = BitVec.ofNat 64 (7776 + 128 * k) ∧ t.gpr .s10 = sig
  have h2 := ctBoth ((pointDecode_ct (b := b) (sp := sp) (inPtr pk sig k) (inBytes PK RS k)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) (A := B1) (B := B2) fun s h =>
      WP.mono (pointDecode_ok h.1.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1) fun t ⟨k', _⟩ =>
        ⟨h.1.1.of_rest k'.rest (by decide), by rw [k'.rest.gpr _ (by decide), h.2.1],
          by rw [k'.rest.gpr _ (by decide), h.2.2]⟩
  have h3 := ctRegs [.a3, .s8, .s10] (A := B2) (c := .block decodeNext)
    (fun _ _ h₁ h₂ => ⟨h₁.1.2.trans h₂.1.2.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1.1.a3, h₂.1.1.a3]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]⟩) (by taint_decide)
  exact RelCT.seq h1 (RelCT.seq h2 h3)

theorem decodeLoop_ct :
    RelCT isa (Both (DecCT b sp pk sig ch PK RS 0)) (.loop decodeBody (.nonzero .a4))
      (Both (DecCT b sp pk sig ch PK RS 2)) := by
  refine (RelCT.loop (Q := Both (DecCT b sp pk sig ch PK RS 2))
    (fun n => Both fun s => 1 ≤ n ∧ n ≤ 2 ∧ DecCT b sp pk sig ch PK RS (2 - n) s) (fun n => ?_) 2).mono
      (fun _ _ h => ⟨⟨by decide, Nat.le_refl _, h.1⟩, ⟨by decide, Nat.le_refl _, h.2⟩⟩) fun _ _ h => h
  by_cases hn : 1 ≤ n ∧ n ≤ 2
  · have hb := ctBoth ((decodeBody_ct (b := b) (sp := sp) (pk := pk) (sig := sig) (ch := ch) (PK := PK) (RS := RS)
      (k := 2 - n)).mono (fun _ _ h => ⟨h.1.2.2, h.2.2.2⟩) fun _ _ h => h)
      (A := fun s => 1 ≤ n ∧ n ≤ 2 ∧ DecCT b sp pk sig ch PK RS (2 - n) s)
      (B := fun t => DecCT b sp pk sig ch PK RS (2 - n + 1) t ∧
        t.gpr .a4 = BitVec.ofNat 64 (7776 + 128 * (2 - n + 1)) - BitVec.ofNat 64 8032)
      fun s ⟨_, _, s0, d, hsp, hpk, hrs⟩ => WP.mono (decodeBody_ok (by omega_using [hn]) d) fun t ⟨dt, e7⟩ =>
        ⟨⟨s0, dt, by rw [dt.rest.sp, ← d.rest.sp, hsp], hpk, hrs⟩, e7⟩
    refine hb.mono (fun _ _ h => h) fun s₁ s₂ ⟨⟨d₁, e₁⟩, ⟨d₂, e₂⟩⟩ =>
      ⟨by rw [eval_nonzero, eval_nonzero, e₁, e₂], fun hf => ?_, fun ht => ?_⟩
    · rcases (by omega_using [hn] : n = 1 ∨ n = 2) with rfl | rfl
      · exact ⟨d₁, d₂⟩
      · rw [eval_nonzero, e₁] at hf; exact absurd hf (by decide)
    · rcases (by omega_using [hn] : n = 1 ∨ n = 2) with rfl | rfl
      · rw [eval_nonzero, e₁] at ht; exact absurd ht (by decide)
      · exact ⟨1, by decide, ⟨by decide, by decide, d₁⟩, ⟨by decide, by decide, d₂⟩⟩
  · exact RelCT.of_false fun _ _ h => hn ⟨h.1.1, h.1.2.1⟩

end

/-! ## The body -/

section
variable {b sp pk sig ch T : Addr} {PK SG CH : List Byte}

/-- The verification's inputs, `PK`, `SG` and `CH`. -/
def VCT (b sp pk sig ch : Addr) (PK SG CH : List Byte) (s : State) : Prop :=
  VCtx b pk sig ch s ∧ s.sp = sp ∧ bytesAt s.mem pk 32 = PK ∧ bytesAt s.mem sig 64 = SG ∧ bytesAt s.mem ch 64 = CH

theorem VCT.frame {s t : State} (h : VCT b sp pk sig ch PK SG CH s) {R : List Reg} (hr' : Rest R s t)
    (hw : ∀ r ∈ [Reg.a3, .s9, .s10, .s11], r ∉ R) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩) : VCT b sp pk sig ch PK SG CH t := by
  refine ⟨h.1.of_rest hr' hw, by rw [hr'.sp, h.2.1], ?_, ?_, ?_⟩
  · rw [bytesAt_ws hf hs h.1.pkD (by decide), h.2.2.1]
  · rw [bytesAt_ws hf hs h.1.sigD (by decide), h.2.2.2.1]
  · rw [bytesAt_ws hf hs h.1.chD (by decide), h.2.2.2.2]

/-- `VCT`, with the static of `-[1]B … -[15]B` at `T`. -/
def VCS (b sp pk sig ch T : Addr) (PK SG CH : List Byte) (s : State) : Prop :=
  VCT b sp pk sig ch PK SG CH s ∧ BStat b T s ∧ s.syms bSym = T

/-- After both decodings. -/
def D2 (b sp pk sig ch T : Addr) (PK SG CH : List Byte) (t : State) : Prop :=
  ∃ s0, DecInv s0 b pk sig ch 2 t ∧ VCS b sp pk sig ch T PK SG CH s0 ∧ t.syms = s0.syms

theorem D2.sp_eq {t : State} (h : D2 b sp pk sig ch T PK SG CH t) : t.sp = sp := by
  obtain ⟨s0, d, ⟨v, _⟩, _⟩ := h; rw [d.rest.sp, v.2.1]

theorem D2.pin {t : State} (h : D2 b sp pk sig ch T PK SG CH t) : Pin b sp t := by
  have hsp := h.sp_eq
  obtain ⟨_, d, _⟩ := h
  exact ⟨d.ctx.ctx, hsp⟩

theorem D2.s4 {t : State} (h : D2 b sp pk sig ch T PK SG CH t) :
    t.gpr .s4 = if ((Spec.Ed25519.decodePoint PK).isSome && (Spec.Ed25519.decodePoint (SG.take 32)).isSome)
      then 1 else 0 := by
  obtain ⟨s0, d, ⟨v, _⟩, _⟩ := h
  have e : decOk s0.mem pk sig 2 = ((Spec.Ed25519.decodePoint (bytesAt s0.mem pk 32)).isSome &&
      (Spec.Ed25519.decodePoint (bytesAt s0.mem sig 32)).isSome) := by
    show (true && (Spec.Ed25519.decodePoint (bytesAt s0.mem (if 0 = 0 then pk else sig) 32)).isSome &&
      (Spec.Ed25519.decodePoint (bytesAt s0.mem (if 1 = 0 then pk else sig) 32)).isSome) = _
    rw [iteT rfl, iteF (by decide), Bool.true_and]
  rw [d.s4, e, v.2.2.1, ← Proof.Ed25519.signatureBytes_take, v.2.2.2.1]

theorem decodeBoth_ct :
    RelCT isa (Both (VCS b sp pk sig ch T PK SG CH)) decodeBoth (Both (D2 b sp pk sig ch T PK SG CH)) := by
  have h := RelCT.seq (ctBoth (ctRegs [.a3, .s9] (A := VCT b sp pk sig ch PK SG CH) (c := .block decodeStart)
    (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.ctx.a3, h₂.1.ctx.a3]
      · rw [h₁.1.s9, h₂.1.s9]⟩) (by taint_decide))
    (B := DecCT b sp pk sig ch PK (SG.take 32) 0) fun s h => WP.mono (decodeStart_ok h.1) fun t d =>
      ⟨s, d, by rw [d.rest.sp, h.2.1], h.2.2.1, by rw [← Proof.Ed25519.signatureBytes_take, h.2.2.2.1]⟩)
    (decodeLoop_ct (b := b) (sp := sp) (pk := pk) (sig := sig) (ch := ch) (PK := PK) (RS := SG.take 32))
  refine ctBoth ((h.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ _ => trivial)) fun s hs => ?_
  unfold decodeBoth at *
  exact WP.mono_syms (decodeBoth_ok hs.1.1) fun t d sy => ⟨s, d, hs, sy⟩

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Ed25519.bytesAt, hi]

end

/-- `verifyRhs`'s precondition: the inputs, the static at `T`, the decoded `a` and `r` in the
tables at 7776 and 7904, and the bytes `CH` of the challenge and `SS` of `S`. -/
def RhsPre (b sp pk sig ch T : Addr) (a r : Spec.Ed25519.Point) (CH SS : List Byte) (t : State) : Prop :=
  VCtx b pk sig ch t ∧ t.sp = sp ∧ BStat b T t ∧ t.syms bSym = T ∧ tableAt t.mem b 7776 = a ∧
    tableAt t.mem b 7904 = r ∧ bytesAt t.mem ch 64 = CH ∧ bytesAt t.mem (sig + BitVec.ofNat 64 32) 32 = SS

/-- **`verifyRhs` leaks only its inputs**, for decoded `a` and `r`: what the windows' proof gives
(`Proof/Ed25519/RISCV64/Whole/VerifyMsgVerified.lean`, `rhs_ct`). -/
def RhsCT : Prop := ∀ {b sp pk sig ch T : Addr} {PK RS CH SS : List Byte} {a r : Spec.Ed25519.Point},
  Spec.Ed25519.decodePoint PK = some a → Spec.Ed25519.decodePoint RS = some r →
  RelCT isa (Both (RhsPre b sp pk sig ch T a r CH SS)) verifyRhs fun _ _ => True

section
variable {b sp pk sig ch T : Addr} {PK SG CH : List Byte}

theorem D2.rhs {t : State} {a r : Spec.Ed25519.Point} (h : D2 b sp pk sig ch T PK SG CH t)
    (ha : Spec.Ed25519.decodePoint PK = some a) (hr : Spec.Ed25519.decodePoint (SG.take 32) = some r) :
    RhsPre b sp pk sig ch T a r CH (SG.drop 32) t := by
  have hsp := h.sp_eq
  obtain ⟨s0, d, ⟨v, hB, hT⟩, sy⟩ := h
  refine ⟨d.ctx, hsp, hB.of_frame d.rest.rd d.frame decW_sub, by rw [sy, hT], ?_, ?_, ?_, ?_⟩
  · exact d.tables 0 (by decide) a (by rw [show inPtr pk sig 0 = pk from rfl, v.2.2.1]; exact ha)
  · exact d.tables 1 (by decide) r (by
      rw [show inPtr pk sig 1 = sig from rfl, ← Proof.Ed25519.signatureBytes_take, v.2.2.2.1]; exact hr)
  · rw [bytesAt_ws d.frame decW_sub d.ctx.chD (by decide), v.2.2.2.2]
  · rw [bytesAt_ws d.frame decW_sub (d.ctx.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide)))
      (by decide), ← Proof.Ed25519.signatureBytes_drop, v.2.2.2.1]

/-- The equation, for the decoded points `a` and `r`. -/
theorem verifyEquationPoints_ct (hRC : RhsCT) {a r : Spec.Ed25519.Point}
    (ha : Spec.Ed25519.decodePoint PK = some a) (hr : Spec.Ed25519.decodePoint (SG.take 32) = some r) :
    RelCT isa (Both (D2 b sp pk sig ch T PK SG CH)) verifyEquationPoints fun _ _ => True := by
  unfold verifyEquationPoints
  exact (hRC (CH := CH) (SS := SG.drop 32) ha hr).mono (fun _ _ h => ⟨h.1.rhs ha hr, h.2.rhs ha hr⟩)
    fun _ _ h => h

theorem verifyDecode_ct (hRC : RhsCT) :
    RelCT isa (Both (VCS b sp pk sig ch T PK SG CH)) verifyDecode fun _ _ => True := by
  unfold verifyDecode
  refine RelCT.seq decodeBoth_ct (RelCT.ite (fun _ _ h => by rw [eval_nonzero, eval_nonzero, h.1.s4, h.2.s4]) ?_ ?_)
  · cases ha : Spec.Ed25519.decodePoint PK with
    | some a =>
      cases hr : Spec.Ed25519.decodePoint (SG.take 32) with
      | some r => exact (verifyEquationPoints_ct hRC ha hr).mono (fun _ _ h => h.1) fun _ _ h => h
      | none =>
        refine RelCT.of_false fun _ _ h => ?_
        have e := h.1.1.s4
        rw [ha, hr] at e
        have := h.2
        rw [eval_nonzero, e] at this
        simp at this
    | none =>
      refine RelCT.of_false fun _ _ h => ?_
      have e := h.1.1.s4
      rw [ha] at e
      have := h.2
      rw [eval_nonzero, e] at this
      simp at this
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.pin, h.1.2.pin⟩) fun _ _ h => h

theorem verifyBody_ct (hRC : RhsCT) :
    RelCT isa (Both (VCS b sp pk sig ch T PK SG CH)) verifyBody fun _ _ => True := by
  unfold verifyBody
  have hFA : ∀ r ∈ [FA b], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_using [])
  have h1 := ctBoth (ctRegs [.a3, .s10] (A := VCS b sp pk sig ch T PK SG CH) (c := .block verifyScalar)
    (fun _ _ h₁ h₂ => ⟨h₁.1.2.1.trans h₂.1.2.1.symm, fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [h₁.1.1.ctx.a3, h₂.1.1.ctx.a3]
      · rw [h₁.1.1.s10, h₂.1.1.s10]⟩) (by taint_decide))
    (B := fun t => VCS b sp pk sig ch T PK SG CH t ∧
      (t.gpr .a5 = 0 ↔ decodeLE (SG.drop 32) < Spec.Ed25519.L))
    fun s h => WP.mono_syms (verifyScalar_ok h.1.1) fun t ⟨rt, ft, et⟩ sy =>
      ⟨⟨h.1.frame rt (by decide) ft hFA, h.2.1.of_frame rt.rd ft hFA, by rw [sy]; exact h.2.2⟩,
        by rw [et, ← Proof.Ed25519.signatureBytes_drop, h.1.2.2.2.1]⟩
  refine RelCT.seq h1 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · have h2 := ctBoth (ctRegs [.a3] (A := VCS b sp pk sig ch T PK SG CH) (c := .block initFields)
      (fun _ _ h₁ h₂ => ⟨h₁.1.2.1.trans h₂.1.2.1.symm, fun x hx => by
        rw [List.mem_singleton.mp hx, h₁.1.1.ctx.a3, h₂.1.1.ctx.a3]⟩) (by taint_decide))
      (B := VCS b sp pk sig ch T PK SG CH) fun s h => WP.mono_syms (initFields_ok h.1.1.ctx.ctx)
        fun t ⟨rt, ft⟩ sy => ⟨h.1.frame rt (by decide) ft hFA, h.2.1.of_frame rt.rd ft hFA, by rw [sy]; exact h.2.2⟩
    exact RelCT.seq (h2.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h) (verifyDecode_ct hRC)
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨⟨h.1.1.1.1.1.ctx, h.1.1.1.1.2.1⟩, ⟨h.1.2.1.1.1.ctx, h.1.2.1.1.2.1⟩⟩)
      fun _ _ h => h

/-- The function's precondition, with its public values. -/
def VTop (b sp pk sig ch T : Addr) (PK SG CH : List Byte) (s : State) : Prop :=
  VerifyPre s ∧ s.syms bSym = T ∧ s.gpr .a0 = pk ∧ s.gpr .a1 = sig ∧ s.gpr .a2 = ch ∧ s.gpr .a3 = b ∧ s.sp = sp ∧
    bytesAt s.mem pk 32 = PK ∧ bytesAt s.mem sig 64 = SG ∧ bytesAt s.mem ch 64 = CH

theorem verifyEquation_rel (hR : RhsOk) (hRC : RhsCT) :
    RelCT isa (Both (VTop b sp pk sig ch T PK SG CH)) Impl.Ed25519.RISCV64.verifyEquation fun _ _ => True := by
  unfold Impl.Ed25519.RISCV64.verifyEquation
  have h1 := ctBoth (ctRegs [.a0, .a1, .a2, .a3] (A := VTop b sp pk sig ch T PK SG CH) (c := .block verifySetup)
    (fun _ _ h₁ h₂ => ⟨h₁.2.2.2.2.2.2.1.trans h₂.2.2.2.2.2.2.1.symm, fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2.1, h₂.2.2.2.1]
      · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
      · rw [h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1]⟩) (by taint_decide))
    (B := VCS b sp pk sig ch T PK SG CH) fun s h => by
      obtain ⟨hp, hT, e3, e4, e5, e6, hsp, hpk, hsg, hch⟩ := h
      refine WP.mono_syms (verifySetup_ok hp) fun t ⟨vt, rt, ft, _⟩ sy => ?_
      have hB := hp.bs
      rw [e6, hT] at hB
      rw [e3, e4, e5, e6] at vt
      rw [e6] at ft
      have hs : ∀ r ∈ [(⟨b, 8192⟩ : Region)], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
        rw [List.mem_singleton.mp hr]; exact fun _ h => h
      refine ⟨⟨vt, by rw [rt.sp, hsp], ?_, ?_, ?_⟩, hB.of_frame rt.rd ft hs, by rw [sy, hT]⟩
      · rw [bytesAt_ws ft hs vt.pkD (by decide), hpk]
      · rw [bytesAt_ws ft hs vt.sigD (by decide), hsg]
      · rw [bytesAt_ws ft hs vt.chD (by decide), hch]
  have h2 := ctBoth (verifyBody_ct (b := b) (sp := sp) (pk := pk) (sig := sig) (ch := ch) (T := T) (PK := PK)
    (SG := SG) (CH := CH) hRC) (B := Pin b sp) fun s h =>
      WP.mono (verifyBody_ok hR h.1.1 (by rw [h.2.2]; exact h.2.1)) fun t ⟨rt, _, _⟩ =>
        Pin.of_rest ⟨h.1.1.ctx, h.1.2.1⟩ rt (by decide)
  exact RelCT.seq h1 (RelCT.seq h2 (ctRegs [.a3] (A := Pin b sp) (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)))

end

end VG.Proof.Ed25519.RISCV64

end

end

/-! ### `Ed25519.RISCV64.Whole.VerifyMsg`, which only this module used -/

section

/-! ### `Ed25519.RISCV64.Whole.VerifyHash`, which only this module used -/

section

/-!
# `vg_ed25519_verify` on RISC-V: the challenge

`pk` in `a0`, the message in `a1` (`len` in `a2`), the signature in `a3`,
`scratch` in `a4` and the frame `F` (272 bytes) in `a5`. The registers
saved at `224(F)`, the signature copied to `128(F)` and `pk` to `192(F)`,
`R ‖ A ‖ M` hashed into `64(F)` (`R` and `A` from their copies), the digest
reduced into `0(F)` by a call of `vg_ed25519_scalar_reduce` and its upper
half zeroed, and the arguments of `verify_equation` set, the copies its
`pk` and signature (`verifyHash_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)

/-- The message. -/
abbrev vmsgR (s : State) : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩

/-- The static of the cached `-[1]B … -[15]B`, which `verify_equation` reads. -/
abbrev vtbR (s : State) : Region := ⟨s.syms Impl.Ed25519.RISCV64.bSym, 1920⟩

/-- The precondition, by register, with the static `vtbR` of `verify_equation`. -/
structure VerPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 32⟩, vmsgR s, ⟨s.gpr .a3, 64⟩, vtbR s]
  wr : s.wr = [⟨s.gpr .a4, 8192⟩, ⟨s.gpr .a5, 272⟩]
  alC : (s.gpr .a4).toNat % 8 = 0
  alF : (s.gpr .a5).toNat % 8 = 0
  pC : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a4, 8192⟩
  pF : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a5, 272⟩
  mC : Region.Disjoint (vmsgR s) ⟨s.gpr .a4, 8192⟩
  mF : Region.Disjoint (vmsgR s) ⟨s.gpr .a5, 272⟩
  sC : Region.Disjoint ⟨s.gpr .a3, 64⟩ ⟨s.gpr .a4, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .a3, 64⟩ ⟨s.gpr .a5, 272⟩
  cF : Region.Disjoint ⟨s.gpr .a4, 8192⟩ ⟨s.gpr .a5, 272⟩
  spal : s.sp.toNat % 16 = 0
  sp : 208 ≤ s.sp.toNat
  bP : (below s.sp 208).Disjoint ⟨s.gpr .a0, 32⟩
  bM : (below s.sp 208).Disjoint (vmsgR s)
  bS : (below s.sp 208).Disjoint ⟨s.gpr .a3, 64⟩
  bC : (below s.sp 208).Disjoint ⟨s.gpr .a4, 8192⟩
  bF : (below s.sp 208).Disjoint ⟨s.gpr .a5, 272⟩
  tfit : (s.syms Impl.Ed25519.RISCV64.bSym).toNat + 1920 ≤ 2 ^ 64
  twords : ∀ q < 240, s.mem.readW (s.syms Impl.Ed25519.RISCV64.bSym + BitVec.ofNat 64 (8 * q)) 64 =
    Impl.Ed25519.RISCV64.bWord q
  tC : (vtbR s).Disjoint ⟨s.gpr .a4, 8192⟩
  tF : (vtbR s).Disjoint ⟨s.gpr .a5, 272⟩
  tB : (vtbR s).Disjoint (below s.sp 208)
  tal : (s.syms Impl.Ed25519.RISCV64.bSym).toNat % 8 = 0

/-- What the body may write. -/
abbrev verW (s : State) : List Region := [⟨s.gpr .a4, 8192⟩, ⟨s.gpr .a5, 272⟩, below s.sp 208]

/-- The values in `s7`–`s10`. -/
def verV (s : State) : Reg → BitVec 64
  | .s7 => s.gpr .a1 | .s8 => s.gpr .a2 | .s9 => s.gpr .a4 | .s10 => s.gpr .a5 | _ => 0

abbrev VerInv (s : State) : State → Prop := Inv s (s.gpr .a5) 224 verifyRegs (verV s) (verW s)

theorem verifyRegs_pres : ∀ r ∈ verifyRegs, r ∈ preserved := by decide

theorem verV_s8 (s : State) : verV s .s8 = s.gpr .a2 := rfl
theorem verV_s9 (s : State) : verV s .s9 = s.gpr .a4 := rfl
theorem verV_s10 (s : State) : verV s .s10 = s.gpr .a5 := rfl

/-- The regions a step may write: the scratch space, the callees' frames, or the frame below the
slots. -/
def VerWr (s : State) (r : Region) : Prop :=
  r = ⟨s.gpr .a4, 8192⟩ ∨ r = below s.sp 208 ∨ ∃ d n, d + n ≤ 224 ∧ r = ⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩

theorem verStep {s t t' : State} (hp : VerPre s) (h : VerInv s t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {Wc : List Region}
    (hf : Frame Wc t.mem t'.mem) (hW : ∀ r ∈ Wc, VerWr s r) : VerInv s t' := by
  obtain hs : Region.Sub (slotArea (s.gpr .a5) 224 verifyRegs) ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  refine Inv.step h verifyRegs_pres hrd hwr hsp hg hf (fun r hr => ?_) fun r hr => ?_
  · rcases hW r hr with rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, Offset.sub_base _ (by omega_using [hdn])⟩
  · rcases hW r hr with rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact hp.cF.symm.sub_left hs
    · exact hp.bF.symm.sub_left hs
    · exact Offset.disjoint _ (.inr hdn) (by decide) (by omega_using [hdn])

/-- An input, while the body runs. -/
theorem ver_input {s t : State} (h : VerInv s t) {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hC : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a4, 8192⟩) (hF : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a5, 272⟩)
    (hB : Region.Disjoint ⟨p, n⟩ (below s.sp 208)) : bytesAt t.mem p n = bytesAt s.mem p n :=
  bytes_keep h.frame hn fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hC
    · exact hF
    · exact hB

theorem ver_env {s t : State} (hp : VerPre s) (h : VerInv s t) : ScEnv (s.gpr .a4) t :=
  ⟨by rw [h.wr, hp.wr]; simp, by rw [h.sp]; exact hp.spal, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩

theorem ver_Fw {s t : State} (hp : VerPre s) (h : VerInv s t) : (⟨s.gpr .a5, 272⟩ : Region) ∈ t.wr := by
  rw [h.wr, hp.wr]; simp

/-- The setup: the registers saved, the pointers moved to `s7`–`s10`, the signature and `pk`
copied. -/
theorem verSetup_ok {s : State} (hp : VerPre s) :
    WP isa (.block (saveRegs .a5 224 verifyRegs ++
      ([mov .s7 .a1, mov .s8 .a2, mov .s9 .a4, mov .s10 .a5] ++ copyIn .a3 .s10 128 64 ++ copyIn .a0 .s10 192)))
      s fun t => VerInv s t ∧
        bytesAt t.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 ∧
        bytesAt t.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
  obtain hF : (⟨s.gpr .a5, 272⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hsl : ∀ p ∈ slots 224 verifyRegs, p.2 + 8 ≤ 272 := by decide
  refine save_ok hp.alF (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega_using [this])) fun u hu hsv hfr => ?_
  unfold mov
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ => ?_
  obtain m₄ : u₄.mem = u.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  obtain g₄ : ∀ r, r ∉ verifyRegs → u₄.gpr r = u.gpr r := fun r hr => by
    simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d⟩ := hr
    rw [h₄.other _ d, h₃.other _ c, h₂.other _ b, h₁.other _ a]
  obtain gu : ∀ r, u.gpr r = s.gpr r := fun r => hu.gpr r (by simp)
  obtain rd₄ : u₄.rd = s.rd := by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd]
  obtain wr₄ : u₄.wr = s.wr := by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr]
  obtain sp₄ : u₄.sp = s.sp := by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp]
  obtain e10 : u₄.gpr .s10 = s.gpr .a5 := by rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide),
    h₁.other _ (by decide), gu]
  obtain hS : (⟨s.gpr .a3, 64⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  obtain hP : (⟨s.gpr .a0, 32⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  -- The signature, then `pk`.
  refine copyIn_ok (P := s.gpr .a3) (F := s.gpr .a5) (o := 128) (n := 64) (by decide) (by decide)
    (by rw [g₄ _ (by decide), gu]) e10 (by decide)
    (fun i hi => by rw [rd₄, wr₄]; exact in_base (List.mem_append_left _ hS) (by omega_using [hi]) (by omega_using [hi]))
    (fun i hi => by rw [wr₄]; exact in_base hF (by omega_using [hi]) (by omega_using [hi]))
    (hp.sF.sub_right (Offset.sub_base _ (by decide))) fun v hv hfv hbv => ?_
  rw [← List.append_nil (copyIn .a0 .s10 192)]
  refine copyIn_ok (P := s.gpr .a0) (F := s.gpr .a5) (o := 192) (n := 32) (by decide) (by decide)
    (by rw [hv.gpr _ (by decide), g₄ _ (by decide), gu]) (by rw [hv.gpr _ (by decide), e10]) (by decide)
    (fun i hi => by rw [hv.rd, hv.wr, rd₄, wr₄]; exact in_base (List.mem_append_left _ hP) (by omega_using [hi]) (by omega_using [hi]))
    (fun i hi => by rw [hv.wr, wr₄]; exact in_base hF (by omega_using [hi]) (by omega_using [hi]))
    (hp.pF.sub_right (Offset.sub_base _ (by decide))) fun t ht hft hbt => WP.block_nil ?_
  obtain F128 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  obtain F192 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  obtain fin : Frame [⟨s.gpr .a5, 272⟩] s.mem t.mem :=
    (hfr.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨⟨s.gpr .a5, 272⟩, by simp, Offset.sub_base _ (by decide)⟩).trans
      ((by rw [m₄] at hfv; exact hfv.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F128⟩ :
        Frame [⟨s.gpr .a5, 272⟩] u.mem v.mem).trans
        (hft.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F192⟩))
  obtain keepIn : ∀ {p : Addr} {n : Nat}, n < 2 ^ 64 → Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a5, 272⟩ →
      bytesAt t.mem p n = bytesAt s.mem p n := fun hn hd =>
    bytes_keep fin hn fun r hr => by rw [List.mem_singleton.mp hr]; exact hd
  refine ⟨⟨by rw [ht.rd, hv.rd, rd₄], by rw [ht.wr, hv.wr, wr₄], by rw [ht.sp, hv.sp, sp₄], fun r hr => ?_,
    fun r hr hn => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [ht.gpr r (by revert hr; decide +revert), hv.gpr r (by revert hr; decide +revert)]
    simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, gu]; rfl
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), gu]; rfl
    · rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
    · rw [e10]; rfl
  · have h5 : r ∉ [Reg.a5] := by
      simp only [List.mem_singleton]; intro e; rw [e] at hr; exact absurd hr (by decide)
    rw [ht.gpr r h5, hv.gpr r h5, g₄ r hn, gu r]
  · refine (hsv.frame_in (slots_in 224 verifyRegs) (m₄ ▸ hfv) fun r hr => ?_).frame_in (slots_in 224 verifyRegs)
      hft fun r hr => ?_
    · rw [List.mem_singleton.mp hr]
      exact (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
    · rw [List.mem_singleton.mp hr]
      exact (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
  · exact fin.mono (by simp)
  · rw [bytes_keep hft (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide), hbv, m₄]
    exact bytes_keep hfr (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hp.sF.sub_right (Offset.sub_base _ (by decide)))
  · rw [hbt]
    obtain e : bytesAt v.mem (s.gpr .a0) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
      rw [bytes_keep hfv (by decide) fun r hr => by
          rw [List.mem_singleton.mp hr]; exact hp.pF.sub_right F128, m₄]
      exact bytes_keep hfr (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.pF.sub_right (Offset.sub_base _ (by decide)))
    exact e

/-- The message's bytes, and `verify`'s challenge. -/
abbrev vmsgB (s : State) : List Byte := bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat

abbrev vChallenge (s : State) : List Byte :=
  Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE (Spec.Sha512.sha512
    (bytesAt s.mem (s.gpr .a3) 32 ++ bytesAt s.mem (s.gpr .a0) 32 ++ vmsgB s)) % Spec.Ed25519.L)

/-- After the challenge: the arguments of `verify_equation`, the copies of `pk` and the signature
its own. -/
structure VerArgs (s t : State) : Prop where
  inv : VerInv s t
  a0 : t.gpr .a0 = s.gpr .a5 + BitVec.ofNat 64 192
  a1 : t.gpr .a1 = s.gpr .a5 + BitVec.ofNat 64 128
  a2 : t.gpr .a2 = s.gpr .a5
  a3 : t.gpr .a3 = s.gpr .a4
  ch : bytesAt t.mem (s.gpr .a5) 64 = vChallenge s
  pk : bytesAt t.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32
  sig : bytesAt t.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64

/-- The copies, through steps that write only the scratch space and the callees' frames. -/
theorem copies_keep {s : State} (hp : VerPre s) {m m' : Mem} {sp : Addr} (hsp : sp = s.sp)
    (hf : Frame [⟨s.gpr .a4, 8192⟩, below sp 208] m m') {d n : Nat} (hd : 128 ≤ d) (hdn : d + n ≤ 224) :
    bytesAt m' (s.gpr .a5 + BitVec.ofNat 64 d) n = bytesAt m (s.gpr .a5 + BitVec.ofNat 64 d) n := by
  subst hsp
  obtain hs : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by omega)
  exact bytes_keep hf (by omega) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.cF.symm.sub_left hs
    · exact hp.bF.symm.sub_left hs

theorem verifyHash_ok (C : ShaOK) {s : State} (hp : VerPre s) : WP isa verifyHash s (VerArgs s) := by
  obtain hlen : (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 := len_add_le (Nat.le_of_lt (s.gpr .a2).isLt) (by decide) hp.mC
  obtain scW : ∀ {t : State}, VerInv s t → ∀ r ∈ [(⟨s.gpr .a4, 8192⟩ : Region), below t.sp 208], VerWr s r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by rw [h.sp]))
  obtain F0 : Region.Sub ⟨s.gpr .a5, 32⟩ ⟨s.gpr .a5, 272⟩ := Region.sub_prefix (by decide)
  obtain F64 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 64, 64⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  obtain F128 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 128, 32⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  obtain F192 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  obtain inRd : ∀ {t : State}, VerInv s t → ∀ {r : Region}, r ∈ s.rd → Covers [r] (t.rd ++ t.wr) :=
    fun h r hr a n hi => by
      obtain ⟨r', hr', hc⟩ := hi
      rw [List.mem_singleton.mp hr'] at hc
      exact ⟨r, List.mem_append_left _ (by rw [h.rd]; exact hr), hc⟩
  obtain inF : ∀ {t : State}, VerInv s t → ∀ {d n : Nat}, d + n ≤ 272 →
      Covers [⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩] (t.rd ++ t.wr) := fun h d n hdn =>
    Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ (ver_Fw hp h), d, rfl, hdn⟩
  unfold verifyHash
  refine WP.seq (WP.mono (verSetup_ok hp) fun t₁ ⟨h₁, cs₁, cp₁⟩ => ?_)
  refine WP.seq (hashInit_ok C (sr := .s9) (h₁.regs _ (by decide)) (ver_env hp h₁)
    fun t₂ a b c f₂ g hr₂ => ?_)
  obtain h₂ := verStep hp h₁ a b c g f₂ (scW h₁)
  obtain cs₂ : bytesAt t₂.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₁.sp f₂ (by decide) (by decide), cs₁]
  obtain cp₂ : bytesAt t₂.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
    rw [copies_keep hp h₁.sp f₂ (by decide) (by decide), cp₁]
  -- `R`, the signature's first half, from its copy.
  refine WP.seq (hashUpdate_ok C (sr := .s9) (src := .s10) (off := 128) (len := 32) (by decide)
    (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide)]; rfl)
    (Sets.li (d := .a1) (k := 0) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (ver_env hp h₂) (inF h₂ (by decide))
    (hp.cF.symm.sub_left F128) (by rw [h₂.sp]; exact hp.bF.sub_right F128) fun t₃ a b c f₃ g hr₃ => ?_)
  obtain h₃ := verStep hp h₂ a b c g f₃ (scW h₂)
  obtain r₃ : Repr t₃.mem (s.gpr .a4) (bytesAt s.mem (s.gpr .a3) 32) := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, ← Proof.Ed25519.signatureBytes_take, cs₂, Proof.Ed25519.signatureBytes_take] at this
  obtain cp₃ : bytesAt t₃.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
    rw [copies_keep hp h₂.sp f₃ (by decide) (by decide), cp₂]
  obtain cs₃ : bytesAt t₃.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₂.sp f₃ (by decide) (by decide), cs₂]
  -- `A`, from its copy.
  refine WP.seq (hashUpdate_ok C (sr := .s9) (src := .s10) (off := 192) (len := 32) (by decide)
    (by decide) (by decide) (h₃.regs _ (by decide)) (by rw [h₃.regs _ (by decide)]; rfl)
    (Sets.li (d := .a1) (k := 32) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (ver_env hp h₃) (inF h₃ (by decide))
    (hp.cF.symm.sub_left F192) (by rw [h₃.sp]; exact hp.bF.sub_right F192) fun t₄ a b c f₄ g hr₄ => ?_)
  obtain h₄ := verStep hp h₃ a b c g f₄ (scW h₃)
  obtain r₄ : Repr t₄.mem (s.gpr .a4) (bytesAt s.mem (s.gpr .a3) 32 ++ bytesAt s.mem (s.gpr .a0) 32) := by
    have := hr₄ _ r₃ (by simp [bytesAt])
    rwa [cp₃] at this
  obtain cs₄ : bytesAt t₄.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₃.sp f₄ (by decide) (by decide), cs₃]
  obtain cp₄ : bytesAt t₄.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
    rw [copies_keep hp h₃.sp f₄ (by decide) (by decide), cp₃]
  -- The message.
  refine WP.seq (hashUpdate_ok C (sr := .s9) (src := .s7) (off := 0) (len := (s.gpr .a2).toNat) (by decide)
    (by decide) (by decide) (h₄.regs _ (by decide))
    (by rw [h₄.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 64) (by decide)) (Sets.mov (d := .a3) (n := .s8))
    (fun _ _ _ => rfl) (fun g g' hg => by rw [hg .s8 (by decide) (by decide) (by decide)])
    (by rw [h₄.regs _ (by decide)]; rfl) (ver_env hp h₄) (inRd h₄ (by rw [hp.rd]; simp))
    hp.mC (by rw [h₄.sp]; exact hp.bM) fun t₅ a b c f₅ g hr₅ => ?_)
  obtain h₅ := verStep hp h₄ a b c g f₅ (scW h₄)
  obtain r₅ : Repr t₅.mem (s.gpr .a4)
      (bytesAt s.mem (s.gpr .a3) 32 ++ bytesAt s.mem (s.gpr .a0) 32 ++ vmsgB s) := by
    have := hr₅ _ r₄ (by simp [bytesAt])
    rwa [ver_input h₄ (s.gpr .a2).isLt hp.mC hp.mF hp.bM.symm] at this
  obtain cs₅ : bytesAt t₅.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₄.sp f₅ (by decide) (by decide), cs₄]
  obtain cp₅ : bytesAt t₅.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
    rw [copies_keep hp h₄.sp f₅ (by decide) (by decide), cp₄]
  refine WP.seq (hashFinalize_ok C (sr := .s9) (f := .s10) (o := 64) (out := s.gpr .a5 + BitVec.ofNat 64 64)
    (vc := fun g => g .s8 + BitVec.ofNat 64 64)
    (by decide) (by decide) (by decide) (h₅.regs _ (by decide))
    (by rw [h₅.regs _ (by decide)]; rfl)
    (Sets.addi (d := .a1) (n := .s8) (k := 64) (by decide)) (fun g g' hg => by rw [hg .s8 (by decide)])
    (ver_env hp h₅)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, ver_Fw hp h₅, 64, rfl, show 64 + 64 ≤ 272 by decide⟩)
    (hp.cF.symm.sub_left F64) (by rw [h₅.sp]; exact hp.bF.sub_right F64) fun t₆ a b c f₆ g hd₆ => ?_)
  obtain h₆ := verStep hp h₅ a b c g f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr ⟨64, 64, by decide, rfl⟩)
    · exact .inr (.inl (by rw [h₅.sp])))
  obtain dg : bytesAt t₆.mem (s.gpr .a5 + BitVec.ofNat 64 64) 64 =
      Spec.Sha512.sha512 (bytesAt s.mem (s.gpr .a3) 32 ++ bytesAt s.mem (s.gpr .a0) 32 ++ vmsgB s) :=
    hd₆ _ r₅ (by simp [bytesAt]; omega_using [hlen])
      (by rw [h₅.regs _ (by decide), cnt_eq, verV_s8]; simp [bytesAt]; congr 1; omega_using [])
  obtain keep6 : ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 224 →
      bytesAt t₆.mem (s.gpr .a5 + BitVec.ofNat 64 d) n = bytesAt t₅.mem (s.gpr .a5 + BitVec.ofNat 64 d) n :=
    fun {d n} hd hdn => bytes_keep f₆ (by omega_using [hdn]) fun r hr => by
      obtain hs : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by omega_using [hdn])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.cF.symm.sub_left hs
      · exact Offset.disjoint _ (.inr (by omega_using [hd])) (by omega_using [hdn]) (by omega_using [])
      · rw [h₅.sp]; exact hp.bF.symm.sub_left hs
  obtain cs₆ := (keep6 (d := 128) (n := 64) (by decide) (by decide)).trans cs₅
  obtain cp₆ := (keep6 (d := 192) (n := 32) (by decide) (by decide)).trans cp₅
  -- `scalar_reduce`.
  obtain ce : ∀ (u : State) q, q ∉ linkRegs → ∀ rd wr, (u.callEntry.withRegions rd wr).gpr q = u.gpr q :=
    fun _ q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  obtain hFw := ver_Fw hp h₆
  obtain hCw : (⟨s.gpr .a4, 8192⟩ : Region) ∈ t₆.wr := (ver_env hp h₆).w
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) fun t₇ k₇ c3 c4 c5 => ?_)
  rw [h₆.regs _ (by decide), verV_s10, BitVec.add_zero] at c3
  rw [h₆.regs _ (by decide), verV_s10] at c4
  rw [h₆.regs _ (by decide), BitVec.add_zero, verV_s9] at c5
  refine WP.seq (WP.call (k := reduceRISCV64) reduce_ok' (rd := [⟨s.gpr .a5 + BitVec.ofNat 64 64, 64⟩])
    (wr := [⟨s.gpr .a5, 32⟩, ⟨s.gpr .a4, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), c4],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), c3, c5],
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c4]; exact Offset.base_disjoint _ (by decide) (by decide),
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c5]; exact hp.cF.symm.sub_left F0,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c4, c5]; exact hp.cF.symm.sub_left F64⟩
    (Covers.of_sub fun r hr => by
      rw [k₇.rd, k₇.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 64, rfl, show 64 + 64 ≤ 272 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₇.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hFw, 0, by simp, by simp⟩
      · exact ⟨_, hCw, 0, by simp, by simp⟩) (fun t₈ a b c f₈ g _ hpost => ?_) (by decide +kernel))
  simp only [reduceRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    c3, c4, k₇.mem, dg] at hpost
  obtain h₈ := verStep hp h₆ (a.trans k₇.rd) (b.trans k₇.wr) (c.trans k₇.sp)
    (fun r hr => (g r hr).trans (k₇.pres r hr)) (k₇.mem ▸ f₈) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr ⟨0, 32, by decide, by simp⟩)
      · exact .inl rfl
  obtain keep8 : ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 224 →
      bytesAt t₈.mem (s.gpr .a5 + BitVec.ofNat 64 d) n = bytesAt t₆.mem (s.gpr .a5 + BitVec.ofNat 64 d) n :=
    fun {d n} hd hdn => by
      rw [← k₇.mem]
      exact bytes_keep f₈ (by omega_using [hdn]) fun r hr => by
        obtain hs : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by omega_using [hdn])
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint_base _ (by omega_using [hd]) (by omega_using [hdn])
        · exact hp.cF.symm.sub_left hs
  obtain cs₈ := (keep8 (d := 128) (n := 64) (by decide) (by decide)).trans cs₆
  obtain cp₈ := (keep8 (d := 192) (n := 32) (by decide) (by decide)).trans cp₆
  -- The upper half zeroed, and the arguments.
  obtain hFw₈ : (⟨s.gpr .a5, 272⟩ : Region) ∈ t₈.wr := ver_Fw hp h₈
  obtain e10 : t₈.gpr .s10 = s.gpr .a5 := h₈.regs _ (by decide)
  obtain inF8 : ∀ (u : State), u.wr = t₈.wr → ∀ d, d + 8 ≤ 272 → InRegions u.wr (s.gpr .a5 + BitVec.ofNat 64 d) 8 :=
    fun u hu d hd => by rw [hu]; exact in_base hFw₈ hd (by omega_using [hd])
  refine wp_li (d := .a5) (imm := 0) (by decide) fun u₁ e₁ => ?_
  refine wp_stdd (a := s.gpr .a5 + BitVec.ofNat 64 32) ⟨by decide, Spill.al8 hp.alF (by decide)⟩
    (by rw [e₁.other _ (by decide), e10]) (inF8 _ e₁.wr 32 (by decide)) fun u₂ e₂ => ?_
  refine wp_stdd (a := s.gpr .a5 + BitVec.ofNat 64 40) ⟨by decide, Spill.al8 hp.alF (by decide)⟩
    (by rw [e₂.gpr, e₁.other _ (by decide), e10]) (inF8 _ (by rw [e₂.wr, e₁.wr]) 40 (by decide)) fun u₃ e₃ => ?_
  refine wp_stdd (a := s.gpr .a5 + BitVec.ofNat 64 48) ⟨by decide, Spill.al8 hp.alF (by decide)⟩
    (by rw [e₃.gpr, e₂.gpr, e₁.other _ (by decide), e10]) (inF8 _ (by rw [e₃.wr, e₂.wr, e₁.wr]) 48 (by decide))
    fun u₄ e₄ => ?_
  refine wp_stdd (a := s.gpr .a5 + BitVec.ofNat 64 56) ⟨by decide, Spill.al8 hp.alF (by decide)⟩
    (by rw [e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e10])
    (inF8 _ (by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr]) 56 (by decide)) fun u₅ e₅ => ?_
  refine wp_addi (by decide) fun v₁ g₁ => wp_addi (by decide) fun v₂ g₂ =>
    wp_addi (by decide) fun v₃ g₃ => wp_addi (by decide) fun v₄ g₄ => WP.block_nil ?_
  have z₁ : u₁.gpr .a5 = 0 := e₁.gpr
  obtain z₂ : u₂.gpr .a5 = 0 := by rw [e₂.gpr, z₁]
  obtain z₃ : u₃.gpr .a5 = 0 := by rw [e₃.gpr, z₂]
  obtain z₄ : u₄.gpr .a5 = 0 := by rw [e₄.gpr, z₃]
  obtain mv : v₄.mem = ((((t₈.mem.writeW (s.gpr .a5 + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW
      (s.gpr .a5 + BitVec.ofNat 64 40) (0 : BitVec 64)).writeW (s.gpr .a5 + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW
      (s.gpr .a5 + BitVec.ofNat 64 56) (0 : BitVec 64)) := by
    rw [g₄.mem, g₃.mem, g₂.mem, g₁.mem, e₅.mem, e₄.mem, e₃.mem, e₂.mem, e₁.mem, z₁, z₂, z₃, z₄]
  obtain gp : ∀ r ∈ preserved, v₄.gpr r = t₈.gpr r := fun r hr => by
    obtain ⟨p0, p1, p2, p3, -⟩ := pres_args hr
    rw [g₄.other _ p3, g₃.other _ p2, g₂.other _ p1, g₁.other _ p0, e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr,
      e₁.other _ (by revert hr; cases r <;> decide)]
  obtain cont : ∀ d, 32 ≤ d → d + 8 ≤ 64 → Region.Contains ⟨s.gpr .a5 + BitVec.ofNat 64 32, 32⟩
      (s.gpr .a5 + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])
  obtain fv : Frame [⟨s.gpr .a5 + BitVec.ofNat 64 32, 32⟩] t₈.mem v₄.mem := by
    rw [mv]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cont 32 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cont 40 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (cont 48 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (cont 56 (by decide) (by decide))
  obtain rr : ∀ (x : Mem) (i j : Nat) (v : BitVec 64), i + 8 ≤ j ∨ j + 8 ≤ i → i + 8 ≤ 272 → j + 8 ≤ 272 →
      (x.writeW (s.gpr .a5 + BitVec.ofNat 64 j) v).readW (s.gpr .a5 + BitVec.ofNat 64 i) 64 =
        x.readW (s.gpr .a5 + BitVec.ofNat 64 i) 64 :=
    fun x i j v h hi hj => Mem.readW_writeW_sep (Offset.sep _ h (by omega_using [hi]) (by omega_using [hj])) (by decide)
  obtain hz : ∀ k < 4, v₄.mem.readW (s.gpr .a5 + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * k)) 64 = 0 := by
    intro k hk
    rw [mv, Offset.add_add]
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega_using [hk]
    rcases this with rfl | rfl | rfl | rfl
    · rw [show 32 + 8 * 0 = 32 from rfl, rr _ 32 56 _ (by decide) (by decide) (by decide),
        rr _ 32 48 _ (by decide) (by decide) (by decide), rr _ 32 40 _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 1 = 40 from rfl, rr _ 40 56 _ (by decide) (by decide) (by decide),
        rr _ 40 48 _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 2 = 48 from rfl, rr _ 48 56 _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 3 = 56 from rfl, Mem.readW_writeW_self64]
  obtain keepv : ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 224 →
      bytesAt v₄.mem (s.gpr .a5 + BitVec.ofNat 64 d) n = bytesAt t₈.mem (s.gpr .a5 + BitVec.ofNat 64 d) n :=
    fun hd hdn => bytes_keep fv (by omega_using [hdn]) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_using [hd])) (by omega_using [hdn]) (by omega_using [])
  refine ⟨verStep hp h₈ (by rw [g₄.rd, g₃.rd, g₂.rd, g₁.rd, e₅.rd, e₄.rd, e₃.rd, e₂.rd, e₁.rd])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr, e₁.wr])
    (by rw [g₄.sp, g₃.sp, g₂.sp, g₁.sp, e₅.sp, e₄.sp, e₃.sp, e₂.sp, e₁.sp]) gp fv fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨32, 32, by decide, rfl⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.other _ (by decide), g₁.gpr,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e10]
  · rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide),
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e10]
  · rw [g₄.other _ (by decide), g₃.gpr, g₂.other _ (by decide), g₁.other _ (by decide), BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e10]
  · rw [g₄.gpr, g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide), BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), h₈.regs _ (by decide)]; rfl
  · have low : bytesAt v₄.mem (s.gpr .a5) 32 = bytesAt t₈.mem (s.gpr .a5) 32 :=
      bytes_keep fv (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint _ (by decide) (by decide)
    rw [Proof.Ed25519.signatureBytes_split, low, hpost, bytes32_zero hz, ← Proof.Ed25519.reduced_challenge]
  · rw [keepv (by decide) (by decide), cp₈]
  · rw [keepv (by decide) (by decide), cs₈]

end VG.Proof.Ed25519.RISCV64.Whole

end

end

/-! ### `Ed25519.RISCV64.VerifyVerified`, which only this module used -/

section

/-!
# `vg_ed25519_verify_equation` on RISC-V, by register

The function meets a contract of its facts by register (`verifyRV`), with no
stack, from a working space aligned to 8 bytes, as an `[u64]` is, and the
static of the cached `-[1]B … -[15]B` (`bSym`, `bWord`): the callers in this
library call it through it. It saves and restores the callee-saved registers
and `ra` (`verify_ok'`), given the windows' proof (`RhsOk`). The contract
declares the inputs and the static's address public, and two runs on the
same inputs leak the same trace (`verifyEquation_rel`, `verify_ct`), given
the windows' constant time (`RhsCT`). What a caller's contract under
`abi.withConsts bConsts` says of the static: `bstat_of_consts`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64

/-- `vg_ed25519_verify_equation`'s contract by register, an internal function's. -/
def verifyRV : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 32⟩
    let sig : Region := ⟨s.gpr .a1, 64⟩
    let ch : Region := ⟨s.gpr .a2, 64⟩
    let ws : Region := ⟨s.gpr .a3, 8192⟩
    let tb : Region := ⟨s.syms bSym, 1920⟩
    s.rd = [pk, sig, ch, tb] ∧ s.wr = [ws] ∧ (s.gpr .a3).toNat % 8 = 0 ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧
      ch.Disjoint ws ∧ (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧ tb.Disjoint ws ∧
      (s.syms bSym).toNat % 8 = 0
  post s s' := (s'.gpr .a0).setWidth 32 = if Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .a0) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .a1) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 64) then 1 else 0
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp ∧
    (Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a0) 32 ++ Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a1) 64 ++
      Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a2) 64).map (·.toNat) =
    (Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .a0) 32 ++ Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .a1) 64 ++
      Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .a2) 64).map (·.toNat) ∧ s₁.syms bSym = s₂.syms bSym

theorem verifyRV_pre {s : State} (hs : verifyRV.pre s) : VerifyPre s :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  ⟨h1, h2, h3, h4, h5, h6, ⟨by rw [h1]; simp, h7, h8, h9, h10⟩⟩

theorem verify_ok' (hR : RhsOk) (s : State) (hs : verifyRV.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed25519.RISCV64.verifyEquation s t s' ∧ abiPreserved s s' ∧
      verifyRV.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hra, hr⟩ := verify_ok hR (verifyRV_pre hs)
  refine ⟨t, s', he, ⟨hg, hsp, hra⟩, ?_⟩
  show (s'.gpr .a0).setWidth 32 = _
  rw [hr]
  split <;> rfl

theorem bytes_of_leak {a₁ b₁ c₁ a₂ b₂ c₂ : List Byte} (ha : a₁.length = a₂.length) (hb : b₁.length = b₂.length)
    (h : (a₁ ++ b₁ ++ c₁).map (·.toNat) = (a₂ ++ b₂ ++ c₂).map (·.toNat)) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  obtain e : a₁ ++ b₁ ++ c₁ = a₂ ++ b₂ ++ c₂ := by
    have := congrArg (List.map fun n => BitVec.ofNat 8 n) h
    simpa [List.map_map, Function.comp_def] using this
  obtain ⟨e1, e2⟩ := List.append_inj e (by simp [ha, hb])
  obtain ⟨e3, e4⟩ := List.append_inj e1 ha
  exact ⟨e3, e4, e2⟩

theorem verify_ct (hR : RhsOk) (hRC : RhsCT) :
    ConstantTime isa verifyRV.pre verifyRV.pub Impl.Ed25519.RISCV64.verifyEquation := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ _ _ _ _ ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨p0, p1, p2, p3, psp, pl, psy⟩ := hp
  obtain hl : ∀ (s : State) (p : Addr) (n : Nat), (Spec.Ed25519.bytesAt s.mem p n).length = n := fun _ _ _ => by
    simp [Spec.Ed25519.bytesAt]
  obtain ⟨b0, b1, b2⟩ := bytes_of_leak (by rw [hl, hl]) (by rw [hl, hl]) pl
  refine verifyEquation_rel hR hRC (b := s₁.gpr .a3) (sp := s₁.sp) (pk := s₁.gpr .a0) (sig := s₁.gpr .a1)
    (ch := s₁.gpr .a2) (T := s₁.syms bSym) (PK := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a0) 32)
    (SG := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a1) 64) (CH := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a2) 64)
    _ _ _ _ _ _ ⟨⟨verifyRV_pre h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨verifyRV_pre h₂, psy.symm, p0.symm, p1.symm, p2.symm, p3.symm, psp.symm, by rw [b0, p0], by rw [b1, p1],
        by rw [b2, p2]⟩⟩ e₁ e₂

theorem bWords_length : bWords.length = 240 := by simp [bWords]

theorem bWords_getD {q : Nat} (hq : q < 240) : bWords.getD q 0 = bWord q := by
  simp [bWords, hq]

/-- What `abi.withConsts [(bSym, ws)]` says of the static, for words `ws` of `bWord`. -/
theorem bstat_of_consts' {st : Nat} {s : State} {ws : List (BitVec 64)} (hl : ws.length = 240)
    (hg : ∀ q < 240, ws.getD q 0 = bWord q) (h : ConstsOk [(bSym, ws)] st s) :
    (⟨s.syms bSym, 1920⟩ : Region) ∈ s.rd ∧ (s.syms bSym).toNat % 8 = 0 ∧ (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 1920⟩ r) ∧
      ∀ r ∈ RISCV64.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 1920⟩ r := by
  have hrd := h.rd1
  obtain hfit := h.fit List.mem_cons_self
  obtain hal := h.aligned List.mem_cons_self
  obtain hd : (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 8 * ws.length⟩ r) ∧
      ∀ r ∈ RISCV64.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 8 * ws.length⟩ r :=
    (h.2.2.1 _ List.mem_cons_self).2
  rw [hl] at hrd hfit hd
  refine ⟨hrd, by omega_using [hal], hfit, fun q hq => ?_, hd.1, hd.2⟩
  rw [h.held1 q (by rw [hl]; exact hq), hg q hq]

/-- What `abi.withConsts bConsts` says of the static. -/
theorem bstat_of_consts {st : Nat} {s : State} (h : ConstsOk bConsts st s) :
    (⟨s.syms bSym, 1920⟩ : Region) ∈ s.rd ∧ (s.syms bSym).toNat % 8 = 0 ∧ (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 1920⟩ r) ∧
      ∀ r ∈ RISCV64.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 1920⟩ r :=
  bstat_of_consts' bWords_length (fun _ hq => bWords_getD hq) h

/-- The readable regions under `abi.withConsts bConsts`: those without it, then the static. -/
theorem rd_of_bconsts' {st : Nat} {s : State} {ws : List (BitVec 64)} {L : List Region}
    (hl : ws.length = 240) (h : ConstsOk [(bSym, ws)] st s)
    (hL : s.rd.take (s.rd.length - 1) = L) : s.rd = L ++ [⟨s.syms bSym, 1920⟩] := by
  have h1 := h.1
  simp only [List.length_singleton, constRegs, Abi.constRegions, List.map_cons, List.map_nil, hl] at h1
  calc s.rd = s.rd.take (s.rd.length - 1) ++ s.rd.drop (s.rd.length - 1) := (List.take_append_drop _ _).symm
    _ = L ++ [⟨s.syms bSym, 1920⟩] := by rw [hL, h1]

theorem rd_of_bconsts {st : Nat} {s : State} {L : List Region} (h : ConstsOk bConsts st s)
    (hL : s.rd.take (s.rd.length - 1) = L) : s.rd = L ++ [⟨s.syms bSym, 1920⟩] :=
  rd_of_bconsts' bWords_length h hL

end VG.Proof.Ed25519.RISCV64

end

end


/-!
# `vg_ed25519_verify` on RISC-V, with its frame as an argument

The challenge (`verifyHash_ok`), the call of `vg_ed25519_verify_equation` on
the copies of `pk` and the signature (`verCall_ok`) and the restores: `a0`
then holds `verify`'s result (`verifyMessage_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)

/-- `verify`'s result on the inputs on entry. -/
abbrev verResult (s : State) : BitVec 32 :=
  if Spec.Ed25519.verify (bytesAt s.mem (s.gpr .a0) 32) (vmsgB s) (bytesAt s.mem (s.gpr .a3) 64) then 1 else 0

/-- The inputs of `verify_equation`: the copies of `pk` and the signature, and the challenge, in `F`. -/
abbrev verRd (s : State) : List Region :=
  [⟨s.gpr .a5 + BitVec.ofNat 64 192, 32⟩, ⟨s.gpr .a5 + BitVec.ofNat 64 128, 64⟩, ⟨s.gpr .a5, 64⟩, vtbR s]

/-- The narrowed state `verify_equation` starts in. -/
theorem verCall_pre {s t : State} (hp : VerPre s) (ha : VerArgs s t) (sy : t.syms = s.syms) :
    verifyRV.pre (t.callEntry.withRegions (verRd s) [⟨s.gpr .a4, 8192⟩]) := by
  obtain ce : ∀ q, q ∉ linkRegs → (t.callEntry.withRegions (verRd s) [⟨s.gpr .a4, 8192⟩]).gpr q = t.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have cy : (t.callEntry.withRegions (verRd s) [⟨s.gpr .a4, 8192⟩]).syms = s.syms := sy
  obtain cm : (t.callEntry.withRegions (verRd s) [⟨s.gpr .a4, 8192⟩]).mem = t.mem := by
    rw [State.withRegions_mem, State.callEntry_mem]
  refine ⟨by rw [State.withRegions_rd, ce _ (by decide), ce _ (by decide), ce _ (by decide), ha.a0, ha.a1, ha.a2, cy],
    by rw [State.withRegions_wr, ce _ (by decide), ha.a3], by rw [ce _ (by decide), ha.a3]; exact hp.alC,
    by rw [ce _ (by decide), ce _ (by decide), ha.a0, ha.a3]; exact hp.cF.symm.sub_left (Offset.sub_base _ (by decide)),
    by rw [ce _ (by decide), ce _ (by decide), ha.a1, ha.a3]; exact hp.cF.symm.sub_left (Offset.sub_base _ (by decide)),
    by rw [ce _ (by decide), ce _ (by decide), ha.a2, ha.a3]; exact hp.cF.symm.sub_left (Region.sub_prefix (by decide)),
    by rw [cy]; exact hp.tfit, fun q hq => ?_, by rw [cy, ce _ (by decide), ha.a3]; exact hp.tC,
    by rw [cy]; exact hp.tal⟩
  rw [cy, cm, ← hp.twords q hq]
  refine ha.inv.frame.readW (r := vtbR s) (Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])) (fun r hr => ?_) (by decide)
  simp only [verW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.tC
  · exact hp.tF
  · exact hp.tB

theorem verCall_covers {s t : State} (hp : VerPre s) (ha : VerArgs s t) :
    Covers (verRd s ++ [⟨s.gpr .a4, 8192⟩]) (t.rd ++ t.wr) ∧ Covers [⟨s.gpr .a4, 8192⟩] t.wr := by
  rw [ha.inv.rd, ha.inv.wr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, 192, rfl, show 192 + 32 ≤ 272 by decide⟩
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, 128, rfl, show 128 + 64 ≤ 272 by decide⟩
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨vtbR s, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .a4, 8192⟩, by simp, 0, by simp, by simp⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨⟨s.gpr .a4, 8192⟩, by simp, 0, by simp, by simp⟩

theorem verifyEquation_noFrames : Impl.Ed25519.RISCV64.verifyEquation.noFrames = true := by decide +kernel

/-- The call of `verify_equation`. -/
theorem verCall_ok (hR : RhsOk) {s t : State} (hp : VerPre s) (ha : VerArgs s t) (sy : t.syms = s.syms) :
    WP isa (.call "vg_ed25519_verify_equation" Impl.Ed25519.RISCV64.verifyEquation) t fun t' =>
      VerInv s t' ∧ (t'.gpr .a0).setWidth 32 = verResult s := by
  obtain ⟨hc, hw⟩ := verCall_covers hp ha
  refine WP.call (k := verifyRV) (verify_ok' hR) (verCall_pre hp ha sy) hc hw (fun t' a b c f g _ hpost => ?_)
    verifyEquation_noFrames
  have hp' : (t'.gpr .a0).setWidth 32 = if Spec.Ed25519.verifyEquation (bytesAt t.mem (t.gpr .a0) 32)
      (bytesAt t.mem (t.gpr .a1) 64) (bytesAt t.mem (t.gpr .a2) 64) then 1 else 0 := hpost
  rw [ha.a0, ha.a1, ha.a2, ha.ch, ha.pk, ha.sig] at hp'
  refine ⟨verStep hp ha.inv a b c g f fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl rfl, hp'.trans ?_⟩
  unfold verResult Spec.Ed25519.verify
  rw [Proof.Ed25519.signatureBytes_take]

theorem verifyMessage_wp (C : ShaOK) (hR : RhsOk) {s : State} (hp : VerPre s) :
    WP isa verifyMessage s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.gpr .ra = s.gpr .ra ∧ (t.gpr .a0).setWidth 32 = verResult s := by
  unfold verifyMessage
  refine WP.seq (WP.mono_syms (verifyHash_ok C hp) fun t ha sy => ?_)
  refine WP.seq (WP.mono (verCall_ok hR hp ha sy) fun t' ⟨h', hr⟩ => ?_)
  obtain hFw : (⟨s.gpr .a5, 272⟩ : Region) ∈ t'.rd ++ t'.wr := List.mem_append_right _ (ver_Fw hp h')
  obtain hrl : ∀ p ∈ restoreList 224 verifyRegs, p.2 + 8 ≤ 272 := by decide
  refine restore_ok h' hp.alF (h'.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => in_base hFw (hrl p hp') (by have := hrl p hp'; omega_using [this]))
    fun t₅ g₅ sp₅ ra₅ _ o₅ => ⟨g₅, sp₅, ra₅, ?_⟩
  rw [o₅ _ (by decide) (by decide), hr]

end VG.Proof.Ed25519.RISCV64.Whole

end

end

/-!
# `vg_ed25519_verify` on RISC-V, with its frame as an argument: by register, and constant time

The contract by register (`verC`), from an aligned `scratch`, and the
proof against it (`ver_ok`). The contract declares the inputs public, and
two runs on the same inputs leak the same trace (`ver_ct`): the taint
analysis checks the challenge's computation (only the pointers and the
length are public to it, and they stay in `s7`–`s10`), and the call of
`verify_equation`, whose branches depend on the inputs, is related by its
own constant time and the arguments' agreement (`RelCT.callEx`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.RISCV64 (bSym bConsts)
open VG.Proof.Ed25519.RISCV64 (bstat_of_consts rd_of_bconsts RhsOk RhsCT)

/-- The contract by register: `pk` in `a0`, the message in `a1` (`len` in `a2`), the signature in
`a3`, `scratch` in `a4`, the frame in `a5`; without the static. -/
def verR : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 32⟩
    let msg : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let sig : Region := ⟨s.gpr .a3, 64⟩
    let sc : Region := ⟨s.gpr .a4, 8192⟩
    let fr : Region := ⟨s.gpr .a5, 272⟩
    s.rd = [pk, msg, sig] ∧ s.wr = [sc, fr] ∧ (s.gpr .a4).toNat % 8 = 0 ∧ (s.gpr .a5).toNat % 8 = 0 ∧
      pk.Disjoint sc ∧ pk.Disjoint fr ∧ msg.Disjoint sc ∧ msg.Disjoint fr ∧ sig.Disjoint sc ∧ sig.Disjoint fr ∧
      sc.Disjoint fr ∧ s.sp.toNat % 16 = 0 ∧ 208 ≤ s.sp.toNat ∧
      (below s.sp 208).Disjoint pk ∧ (below s.sp 208).Disjoint msg ∧ (below s.sp 208).Disjoint sig ∧
      (below s.sp 208).Disjoint sc ∧ (below s.sp 208).Disjoint fr
  post s s' := (s'.gpr .a0).setWidth 32 = verResult s
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp ∧
    (bytesAt s₁.mem (s₁.gpr .a0) 32 ++ bytesAt s₁.mem (s₁.gpr .a1) (s₁.gpr .a2).toNat ++
      bytesAt s₁.mem (s₁.gpr .a3) 64).map (·.toNat) =
    (bytesAt s₂.mem (s₂.gpr .a0) 32 ++ bytesAt s₂.mem (s₂.gpr .a1) (s₂.gpr .a2).toNat ++
      bytesAt s₂.mem (s₂.gpr .a3) 64).map (·.toNat)

/-- `verR` with the static of `verify_equation` (`abi.withConsts bConsts`). -/
def verC : Contract isa where
  pre s := verR.pre (stripConsts bConsts s) ∧ ConstsOk bConsts 208 s
  post := verR.post
  pub s₁ s₂ := verR.pub s₁ s₂ ∧ s₁.syms bSym = s₂.syms bSym

theorem verC_pre {s : State} (h : verC.pre s) : VerPre s := by
  obtain ⟨⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p, q, r⟩, hk⟩ := h
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at *
  obtain ⟨-, tal, tfit, words, twr, tres⟩ := bstat_of_consts hk
  have hrd : s.rd = [⟨s.gpr .a0, 32⟩, vmsgR s, ⟨s.gpr .a3, 64⟩, vtbR s] := rd_of_bconsts hk a
  have hB : below s.sp 208 ∈ RISCV64.abi.reserved 208 s := by
    show _ ∈ stackBelow s.sp 208
    rw [stackBelow_pos _ (by decide)]; simp
  exact ⟨hrd, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p, q, r, tfit, words, twr _ (by rw [b]; simp),
    twr _ (by rw [b]; simp), tres _ hB, tal⟩

theorem ver_ok (hR : RhsOk) (s : State) (hs : verC.pre s) :
    ∃ t s', Exec isa verifyMessage s t s' ∧ abiPreserved s s' ∧ verC.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ := verifyMessage_wp sha512OK hR (verC_pre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hq⟩

/-- Two runs on the same public data, as `RelCT.constantTime` relates them. -/
abbrev VP (s₁ s₂ : State) : Prop := verC.pre s₁ ∧ verC.pre s₂ ∧ verC.pub s₁ s₂

/-- The inputs agree in two such runs. -/
theorem vp_bytes {s₁ s₂ : State} (h : VP s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .a0) 32 = bytesAt s₂.mem (s₂.gpr .a0) 32 ∧ vmsgB s₁ = vmsgB s₂ ∧
      bytesAt s₁.mem (s₁.gpr .a3) 64 = bytesAt s₂.mem (s₂.gpr .a3) 64 := by
  obtain ⟨-, -, ⟨-, -, p2, -, -, -, -, pl⟩, -⟩ := h
  have hl : ∀ (s : State) (p : Addr) (n : Nat), (bytesAt s.mem p n).length = n := fun _ _ _ => by
    simp [bytesAt]
  exact bytes_of_leak (by rw [hl, hl]) (by rw [hl, hl, p2]) pl

/-- The restores, with `F` in `s10` in both runs. -/
theorem restore_ct {P : State → State → Prop}
    (hp : ∀ t₁ t₂, P t₁ t₂ → t₁.sp = t₂.sp ∧ t₁.gpr .s10 = t₂.gpr .s10) :
    RelCT isa P (.block (restoreRegs .s10 224 verifyRegs)) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.s10]) (fun t₁ t₂ h => ⟨(hp _ _ h).1, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr; exact (hp _ _ h).2⟩) (by taint_decide)

/-- Two runs' entry states. -/
abbrev VPair : Type := {σ : State × State // VP σ.1 σ.2}

theorem ver_ct (hR : RhsOk) (hRC : RhsCT) : ConstantTime isa verC.pre verC.pub verifyMessage := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold verifyMessage
  refine RelCT.seq (R := fun (t₁ t₂ : State) => ∃ σ : VPair, (VerArgs σ.1.1 t₁ ∧ t₁.syms = σ.1.1.syms) ∧
    (VerArgs σ.1.2 t₂ ∧ t₂.syms = σ.1.2.syms)) ?_ <|
    RelCT.seq (R := fun t₁ t₂ => ∃ σ : VPair, VerInv σ.1.1 t₁ ∧ VerInv σ.1.2 t₂) ?_ ?_
  · refine ((RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (fun s₁ s₂ h => ?_)
      (by taint_decide)).wpDep (F := fun (s t : State) => VerArgs s t ∧ t.syms = s.syms) fun s₁ s₂ h =>
        ⟨WP.mono_syms (verifyHash_ok sha512OK (verC_pre h.1)) fun _ a sy => ⟨a, sy⟩,
          WP.mono_syms (verifyHash_ok sha512OK (verC_pre h.2.1)) fun _ a sy => ⟨a, sy⟩⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨⟨(σ₁, σ₂), hp⟩, a₁, a₂⟩
    obtain ⟨-, -, ⟨p0, p1, p2, p3, p4, p5, psp, -⟩, -⟩ := h
    refine ⟨psp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine RelCT.exists_ fun σ => ?_
    refine ((RelCT.callEx (k := verifyRV) (verify_ok' hR) (verify_ct hR hRC)
      fun t₁ t₂ ⟨⟨a₁, y₁⟩, ⟨a₂, y₂⟩⟩ => ?_).wp
      (F₁ := VerInv σ.1.1) (F₂ := VerInv σ.1.2) fun t₁ t₂ ⟨⟨a₁, y₁⟩, ⟨a₂, y₂⟩⟩ =>
        ⟨WP.mono (verCall_ok hR (verC_pre σ.2.1) a₁ y₁) fun _ h => h.1,
          WP.mono (verCall_ok hR (verC_pre σ.2.2.1) a₂ y₂) fun _ h => h.1⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, i₁, i₂⟩ => ⟨σ, i₁, i₂⟩
    have hp₁ := verC_pre σ.2.1
    have hp₂ := verC_pre σ.2.2.1
    obtain ⟨c₁, w₁⟩ := verCall_covers hp₁ a₁
    obtain ⟨c₂, w₂⟩ := verCall_covers hp₂ a₂
    refine ⟨_, _, _, _, verCall_pre hp₁ a₁ y₁, verCall_pre hp₂ a₂ y₂, ?_, c₁, w₁, c₂, w₂⟩
    obtain ⟨-, -, ⟨p0, p1, p2, p3, p4, p5, psp, -⟩, psy⟩ := σ.2
    obtain ⟨b0, bm, b3⟩ := vp_bytes σ.2
    have ch : vChallenge σ.1.1 = vChallenge σ.1.2 := by
      unfold vChallenge
      rw [← Proof.Ed25519.signatureBytes_take, ← Proof.Ed25519.signatureBytes_take σ.1.2.mem, b3, b0, bm]
    simp only [verifyRV, State.withRegions_gpr, State.withRegions_sp, State.withRegions_mem, State.callEntry_sp,
      State.callEntry_mem, State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide)]
    rw [a₁.a0, a₂.a0, a₁.a1, a₂.a1, a₁.a2, a₂.a2, a₁.a3, a₂.a3, a₁.inv.sp, a₂.inv.sp, a₁.ch, a₂.ch,
      a₁.pk, a₂.pk, a₁.sig, a₂.sig, b0, b3, ch]
    exact ⟨by rw [p5], by rw [p5], p5, p4, psp, rfl, by
      show t₁.syms bSym = t₂.syms bSym
      rw [y₁, y₂]; exact psy⟩
  · exact RelCT.exists_ fun σ => restore_ct fun t₁ t₂ ⟨i₁, i₂⟩ => by
      obtain ⟨-, -, ⟨-, -, -, -, -, p5, psp, -⟩, -⟩ := σ.2
      exact ⟨by rw [i₁.sp, i₂.sp]; exact psp, by
        rw [i₁.regs .s10 (by decide), i₂.regs .s10 (by decide), verV_s10, verV_s10]
        exact p5⟩

end VG.Proof.Ed25519.RISCV64.Whole
