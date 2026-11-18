module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyFn
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Decode
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyPoints
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyFn
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Decode
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyPoints
meta import VerifiedGarbage.Proof.X25519.RISCV64.Instr
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Spec.Ed25519.Contract

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
