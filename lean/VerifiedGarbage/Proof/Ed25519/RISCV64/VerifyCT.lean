module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.DecodeCT
public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldTest
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointScalar
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.DecodeCT
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyFn
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldTest
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.PointScalar
meta import VerifiedGarbage.Proof.X25519.RISCV64.Instr
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.RISCV64.Decode
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Decode

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

section
variable {b sp : Addr}

/-- Before the comparison: the points `p` and `q` in slots 0–3 and 4–7. -/
def EqPre (b sp : Addr) (p q : Spec.Ed25519.Point) (s : State) : Prop :=
  Pin b sp s ∧ point (env s.mem b) 0 1 2 3 = p ∧ point (env s.mem b) 4 5 6 7 = q

theorem pointEqual_ct (p q : Spec.Ed25519.Point) :
    RelCT isa (Both (EqPre b sp p q)) Impl.Ed25519.RISCV64.pointEqual fun _ _ => True := by
  unfold Impl.Ed25519.RISCV64.pointEqual
  let E (t : State) : Prop := Pin b sp t ∧ env t.mem b 8 = p.X * q.Z ∧ env t.mem b 9 = q.X * p.Z ∧
    env t.mem b 10 = p.Y * q.Z ∧ env t.mem b 11 = q.Y * p.Z
  have h1 := ctBoth (ctRegs [.a3] (A := EqPre b sp p q) (c := fieldCode pointEqualOps)
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide)) (B := E) fun s h =>
      WP.mono (fieldCode_ok _ h.1.1.ctx h.1.1.ws) fun t ⟨k, e⟩ => by
        refine ⟨h.1.of_rest k.rest (by decide), ?_, ?_, ?_, ?_⟩ <;> rw [e, ← h.2.1, ← h.2.2] <;> rfl
  let E' (t : State) : Prop := Pin b sp t ∧ env t.mem b 10 = p.Y * q.Z ∧ env t.mem b 11 = q.Y * p.Z
  have h2 := ctBoth (ctRegs [.a3] (A := E) (c := fieldEqual 8 9) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => E' t ∧ (t.gpr .a2 = 0 ↔ p.X * q.Z = q.X * p.Z)) fun s h =>
      WP.mono (fieldEqual_ok h.1.1.ctx h.1.1.ws 8 9) fun t ⟨k, e, z⟩ =>
        ⟨⟨h.1.of_rest k.rest (by decide), by rw [e]; exact h.2.2.2.1, by rw [e]; exact h.2.2.2.2⟩,
          by rw [z, h.2.1, h.2.2.1]⟩
  have h3 := ctBoth (ctRegs [.a3] (A := E') (c := fieldEqual 10 11) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => Pin b sp t ∧ (t.gpr .a2 = 0 ↔ p.Y * q.Z = q.Y * p.Z)) fun s h =>
      WP.mono (fieldEqual_ok h.1.1.ctx h.1.1.ws 10 11) fun t ⟨k, _, z⟩ =>
        ⟨h.1.of_rest k.rest (by decide), by rw [z, h.2.1, h.2.2]⟩
  refine RelCT.seq h1 (RelCT.seq h2 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_))
  · refine RelCT.seq (h3.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
      (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
    · exact (ctRegs [.a3] (A := Pin b sp) (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)).mono
        (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h

end

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
        exact ⟨fun j hj => in_base (List.mem_append_left _ hv1.pkR) (by omega) (by omega), hv1.pkD, hpk⟩
      · rw [iteF h0, iteF h0]
        exact ⟨fun j hj => in_base (List.mem_append_left _ hv1.sigR) (by omega) (by omega),
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
      fun s ⟨_, _, s0, d, hsp, hpk, hrs⟩ => WP.mono (decodeBody_ok (by omega) d) fun t ⟨dt, e7⟩ =>
        ⟨⟨s0, dt, by rw [dt.rest.sp, ← d.rest.sp, hsp], hpk, hrs⟩, e7⟩
    refine hb.mono (fun _ _ h => h) fun s₁ s₂ ⟨⟨d₁, e₁⟩, ⟨d₂, e₂⟩⟩ =>
      ⟨by rw [eval_nonzero, eval_nonzero, e₁, e₂], fun hf => ?_, fun ht => ?_⟩
    · rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl
      · exact ⟨d₁, d₂⟩
      · rw [eval_nonzero, e₁] at hf; exact absurd hf (by decide)
    · rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl
      · rw [eval_nonzero, e₁] at ht; exact absurd ht (by decide)
      · exact ⟨1, by decide, ⟨by decide, by decide, d₁⟩, ⟨by decide, by decide, d₂⟩⟩
  · exact RelCT.of_false fun _ _ h => hn ⟨h.1.1, h.1.2.1⟩

end

/-! ## The body -/

section
variable {b sp pk sig ch : Addr} {PK SG CH : List Byte}

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

/-- After both decodings. -/
def D2 (b sp pk sig ch : Addr) (PK SG CH : List Byte) (t : State) : Prop :=
  ∃ s0, DecInv s0 b pk sig ch 2 t ∧ VCT b sp pk sig ch PK SG CH s0

theorem D2.sp_eq {t : State} (h : D2 b sp pk sig ch PK SG CH t) : t.sp = sp := by
  obtain ⟨s0, d, v⟩ := h; rw [d.rest.sp, v.2.1]

theorem D2.pin {t : State} (h : D2 b sp pk sig ch PK SG CH t) : Pin b sp t := by
  have hsp := h.sp_eq
  obtain ⟨_, d, _⟩ := h
  exact ⟨d.ctx.ctx, hsp⟩

theorem D2.s4 {t : State} (h : D2 b sp pk sig ch PK SG CH t) :
    t.gpr .s4 = if ((Spec.Ed25519.decodePoint PK).isSome && (Spec.Ed25519.decodePoint (SG.take 32)).isSome)
      then 1 else 0 := by
  obtain ⟨s0, d, v⟩ := h
  have e : decOk s0.mem pk sig 2 = ((Spec.Ed25519.decodePoint (bytesAt s0.mem pk 32)).isSome &&
      (Spec.Ed25519.decodePoint (bytesAt s0.mem sig 32)).isSome) := by
    show (true && (Spec.Ed25519.decodePoint (bytesAt s0.mem (if 0 = 0 then pk else sig) 32)).isSome &&
      (Spec.Ed25519.decodePoint (bytesAt s0.mem (if 1 = 0 then pk else sig) 32)).isSome) = _
    rw [iteT rfl, iteF (by decide), Bool.true_and]
  rw [d.s4, e, v.2.2.1, ← Proof.Ed25519.signatureBytes_take, v.2.2.2.1]

theorem decodeBoth_ct :
    RelCT isa (Both (VCT b sp pk sig ch PK SG CH)) decodeBoth (Both (D2 b sp pk sig ch PK SG CH)) := by
  have h := RelCT.seq (ctBoth (ctRegs [.a3, .s9] (A := VCT b sp pk sig ch PK SG CH) (c := .block decodeStart)
    (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.ctx.a3, h₂.1.ctx.a3]
      · rw [h₁.1.s9, h₂.1.s9]⟩) (by taint_decide))
    (B := DecCT b sp pk sig ch PK (SG.take 32) 0) fun s h => WP.mono (decodeStart_ok h.1) fun t d =>
      ⟨s, d, by rw [d.rest.sp, h.2.1], h.2.2.1, by rw [← Proof.Ed25519.signatureBytes_take, h.2.2.2.1]⟩)
    (decodeLoop_ct (b := b) (sp := sp) (pk := pk) (sig := sig) (ch := ch) (PK := PK) (RS := SG.take 32))
  refine ctBoth (h.mono (fun _ _ h => h) fun _ _ _ => trivial) fun s hs => ?_
  unfold decodeBoth at *
  exact WP.mono (decodeBoth_ok hs.1) fun t d => ⟨s, d, hs⟩

/-- `[S] B` leaves the tables of `A` and `R`. -/
theorem sideW_tables {o : Nat} (ho : 7776 ≤ o) (ho' : o + 128 ≤ 8032) :
    ∀ r ∈ sideW b 8032, Region.Disjoint ⟨b + BitVec.ofNat 64 o, 128⟩ r := by
  intro r hr
  have hB : BITSB = 32 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Ed25519.bytesAt, hi]

/-- `[k] A + R`, before the comparison: the taint analysis checks each piece, and the
branch on the challenge's top half is taken on the same bytes `CH` in both runs. -/
theorem rhsPre_ct {pk sig ch : Addr} {CH : List (BitVec 8)} {A : State → Prop}
    (hA : ∀ t, A t → VCtx b pk sig ch t ∧ t.sp = sp ∧ bytesAt t.mem ch 64 = CH) :
    RelCT isa (Both A)
      (.seq (.seq (.block (pointTableRead 7776 ++ ([.addi .s0 .s11 0] : List Instr))) challengeMul)
        verifyCombine) fun _ _ => True := by
  let M1 (t : State) : Prop := VCtx b pk sig ch t ∧ t.sp = sp ∧ t.gpr .s0 = ch ∧ bytesAt t.mem ch 64 = CH
  let M2 (t : State) : Prop := M1 t ∧ (t.gpr .a4 = 0 ↔ ∀ i < 32, CH.getD (32 + i) 0 = 0)
  let Mid (t : State) : Prop := Ctx8 b t ∧ t.sp = sp
  have hX : RelCT isa (Both A) (.block (pointTableRead 7776 ++ ([.addi .s0 .s11 0] : List Instr))) (Both M1) :=
    ctBoth (ctRegs [.a3, .s11] (A := A) (fun _ _ h₁ h₂ => ⟨(hA _ h₁).2.1.trans (hA _ h₂).2.1.symm,
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [(hA _ h₁).1.ctx.ctx.a3, (hA _ h₂).1.ctx.ctx.a3]
        · rw [(hA _ h₁).1.s11, (hA _ h₂).1.s11]⟩) (by taint_decide))
      fun s h => WP.mono (rhsLoad_ok (hA s h).1) fun t ⟨rt, _, e0, vt, bt⟩ =>
        ⟨vt, by rw [rt.sp, (hA s h).2.1], e0, by rw [bt, (hA s h).2.2]⟩
  have hCH : RelCT isa (Both M1) (.block challengeHigh) (Both M2) :=
    ctBoth (ctRegs [.a3, .s0, .s11] (A := M1) (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm,
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1.ctx.ctx.a3, h₂.1.ctx.ctx.a3]
        · rw [h₁.2.2.1, h₂.2.2.1]
        · rw [h₁.1.s11, h₂.1.s11]⟩) (by taint_decide))
      fun s h => WP.mono (challengeHigh_ok (ch := ch) h.1.s11
        (fun i hi => in_base (List.mem_append_left _ h.1.chR) (by omega) (by omega)))
        fun t ⟨rt, mt, et⟩ => ⟨⟨h.1.of_rest rt (by decide), by rw [rt.sp, h.2.1],
          by rw [rt.gpr _ (by decide), h.2.2.1], by rw [mt, h.2.2.2]⟩, by
          rw [et, ← h.2.2.2]
          exact forall_congr' fun i => imp_congr_right fun hi => by rw [bytesAt_getD _ _ (by omega)]⟩
  have pub2 : ∀ s₁ s₂, M2 s₁ → M2 s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a3, .s0], s₁.gpr r = s₂.gpr r :=
    fun _ _ h₁ h₂ => ⟨h₁.1.2.1.trans h₂.1.2.1.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.ctx.ctx.a3, h₂.1.1.ctx.ctx.a3]
      · rw [h₁.1.2.2.1, h₂.1.2.2.1]⟩
  have post : ∀ n, 1 ≤ n → n ≤ 32 → ∀ s, M2 s → WP isa (pointFromScalar n) s Mid := fun n h1 h32 s h =>
    WP.mono (pointFromScalar_ok h.1.1.ctx (count := n) h1 h32 h.1.2.2.1
      (fun i hi => in_base (List.mem_append_left _ h.1.1.chR) (by omega) (by omega))
      (h.1.1.chD.sub_left (Region.sub_prefix (by omega))))
      fun t ⟨rt, _, _, _⟩ => ⟨h.1.1.ctx.of_rest rt (by decide), by rw [rt.sp, h.1.2.1]⟩
  have h16 : RelCT isa (Both M2) (pointFromScalar 16) (Both Mid) :=
    ctBoth (ctRegs [.a3, .s0] (A := M2) pub2 (by taint_decide)) (post 16 (by decide) (by decide))
  have h32 : RelCT isa (Both M2) (pointFromScalar 32) (Both Mid) :=
    ctBoth (ctRegs [.a3, .s0] (A := M2) pub2 (by taint_decide)) (post 32 (by decide) (by decide))
  have hite : RelCT isa (Both M2) (.ite (.zero .a4) (pointFromScalar 16) (pointFromScalar 32)) (Both Mid) :=
    RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) (h16.mono (fun _ _ h => h.1) fun _ _ h => h)
      (h32.mono (fun _ _ h => h.1) fun _ _ h => h)
  have hVC : RelCT isa (Both Mid) verifyCombine fun _ _ => True :=
    ctRegs [.a3] (A := Mid) (fun _ _ h₁ h₂ => ⟨h₁.2.trans h₂.2.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h₁.1.a3, h₂.1.a3]⟩) (by taint_decide)
  unfold challengeMul
  exact RelCT.seq (RelCT.seq hX (RelCT.seq hCH hite)) hVC

/-- The equation, for the decoded points `a` and `r`. -/
theorem verifyEquationPoints_ct {a r : Spec.Ed25519.Point} (ha : Spec.Ed25519.decodePoint PK = some a)
    (hr : Spec.Ed25519.decodePoint (SG.take 32) = some r) :
    RelCT isa (Both (D2 b sp pk sig ch PK SG CH)) verifyEquationPoints fun _ _ => True := by
  let lhs := Spec.Ed25519.pointMul (decodeLE (SG.drop 32)) Spec.Ed25519.basePoint
  let L1 (t : State) : Prop := VCtx b pk sig ch t ∧ t.sp = sp ∧ tableAt t.mem b 8032 = lhs ∧
    tableAt t.mem b 7776 = a ∧ tableAt t.mem b 7904 = r ∧ bytesAt t.mem ch 64 = CH
  have h1 := ctBoth (ctRegs [.a3, .s10] (A := D2 b sp pk sig ch PK SG CH) (c := verifyLhs)
    (fun _ _ h₁ h₂ => ⟨h₁.sp_eq.trans h₂.sp_eq.symm, fun x hx => by
      obtain ⟨_, d₁, _⟩ := h₁
      obtain ⟨_, d₂, _⟩ := h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [d₁.ctx.ctx.a3, d₂.ctx.ctx.a3]
      · rw [d₁.ctx.s10, d₂.ctx.s10]⟩) (by taint_decide)) (B := L1) fun s hs => by
    have hsp := hs.sp_eq
    obtain ⟨s0, d, v⟩ := hs
    have hS : bytesAt s.mem (sig + BitVec.ofNat 64 32) 32 = SG.drop 32 := by
      rw [bytesAt_ws d.frame decW_sub (d.ctx.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide)))
        (by decide), ← Proof.Ed25519.signatureBytes_drop, v.2.2.2.1]
    refine WP.mono (verifyLhs_ok d.ctx) fun t ⟨rt, ft, tt⟩ => ⟨d.ctx.of_rest rt (by decide), by rw [rt.sp, hsp],
      by rw [tt, hS], ?_, ?_, ?_⟩
    · rw [tableAt_keep ft (sideW_tables (by decide) (by decide))]
      exact d.tables 0 (by decide) a (by rw [show inPtr pk sig 0 = pk from rfl, v.2.2.1]; exact ha)
    · rw [tableAt_keep ft (sideW_tables (by decide) (by decide))]
      exact d.tables 1 (by decide) r (by
        rw [show inPtr pk sig 1 = sig from rfl, ← Proof.Ed25519.signatureBytes_take, v.2.2.2.1]; exact hr)
    · rw [bytesAt_ws ft (sideW_sub (by decide)) d.ctx.chD (by decide),
        bytesAt_ws d.frame decW_sub d.ctx.chD (by decide), v.2.2.2.2]
  let sum := Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (decodeLE CH) a)
  have hpre := ctBoth (rhsPre_ct (A := L1) (CH := CH) fun t h => ⟨h.1, h.2.1, h.2.2.2.2.2⟩) (B := EqPre b sp lhs sum) fun s h =>
      WP.mono (verifyRhsPre_ok' h.1) fun t ⟨rt, _, ct, pt, qt⟩ =>
        ⟨⟨ct, by rw [rt.sp, h.2.1]⟩, by rw [pt, h.2.2.1], by rw [qt, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]⟩
  unfold verifyEquationPoints verifyRhs
  exact RelCT.seq h1 (RelCT.assoc (RelCT.assoc (RelCT.seq hpre (pointEqual_ct lhs sum))))

theorem verifyDecode_ct :
    RelCT isa (Both (VCT b sp pk sig ch PK SG CH)) verifyDecode fun _ _ => True := by
  unfold verifyDecode
  refine RelCT.seq decodeBoth_ct (RelCT.ite (fun _ _ h => by rw [eval_nonzero, eval_nonzero, h.1.s4, h.2.s4]) ?_ ?_)
  · cases ha : Spec.Ed25519.decodePoint PK with
    | some a =>
      cases hr : Spec.Ed25519.decodePoint (SG.take 32) with
      | some r => exact (verifyEquationPoints_ct ha hr).mono (fun _ _ h => h.1) fun _ _ h => h
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

theorem verifyBody_ct :
    RelCT isa (Both (VCT b sp pk sig ch PK SG CH)) verifyBody fun _ _ => True := by
  unfold verifyBody
  have hFA : ∀ r ∈ [FA b], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega)
  have h1 := ctBoth (ctRegs [.a3, .s10] (A := VCT b sp pk sig ch PK SG CH) (c := .block verifyScalar)
    (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [h₁.1.ctx.a3, h₂.1.ctx.a3]
      · rw [h₁.1.s10, h₂.1.s10]⟩) (by taint_decide))
    (B := fun t => VCT b sp pk sig ch PK SG CH t ∧ (t.gpr .a5 = 0 ↔ decodeLE (SG.drop 32) < Spec.Ed25519.L))
    fun s h => WP.mono (verifyScalar_ok h.1) fun t ⟨rt, ft, et⟩ =>
      ⟨h.frame rt (by decide) ft hFA, by rw [et, ← Proof.Ed25519.signatureBytes_drop, h.2.2.2.1]⟩
  refine RelCT.seq h1 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · have h2 := ctBoth (ctRegs [.a3] (A := VCT b sp pk sig ch PK SG CH) (c := .block initFields)
      (fun _ _ h₁ h₂ => ⟨h₁.2.1.trans h₂.2.1.symm, fun x hx => by
        rw [List.mem_singleton.mp hx, h₁.1.ctx.a3, h₂.1.ctx.a3]⟩) (by taint_decide))
      (B := VCT b sp pk sig ch PK SG CH) fun s h => WP.mono (initFields_ok h.1.ctx.ctx) fun t ⟨rt, ft⟩ =>
        h.frame rt (by decide) ft hFA
    exact RelCT.seq (h2.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h) verifyDecode_ct
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨⟨h.1.1.1.1.ctx, h.1.1.1.2.1⟩, ⟨h.1.2.1.1.ctx, h.1.2.1.2.1⟩⟩)
      fun _ _ h => h

/-- The function's precondition, with its public values. -/
def VTop (b sp pk sig ch : Addr) (PK SG CH : List Byte) (s : State) : Prop :=
  VerifyPre s ∧ s.gpr .a0 = pk ∧ s.gpr .a1 = sig ∧ s.gpr .a2 = ch ∧ s.gpr .a3 = b ∧ s.sp = sp ∧
    bytesAt s.mem pk 32 = PK ∧ bytesAt s.mem sig 64 = SG ∧ bytesAt s.mem ch 64 = CH

theorem verifyEquation_rel :
    RelCT isa (Both (VTop b sp pk sig ch PK SG CH)) Impl.Ed25519.RISCV64.verifyEquation fun _ _ => True := by
  unfold Impl.Ed25519.RISCV64.verifyEquation
  have h1 := ctBoth (ctRegs [.a0, .a1, .a2, .a3] (A := VTop b sp pk sig ch PK SG CH) (c := .block verifySetup)
    (fun _ _ h₁ h₂ => ⟨h₁.2.2.2.2.2.1.trans h₂.2.2.2.2.2.1.symm, fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2.1, h₂.2.2.2.1]
      · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]⟩) (by taint_decide))
    (B := VCT b sp pk sig ch PK SG CH) fun s h => by
      obtain ⟨hp, e3, e4, e5, e6, hsp, hpk, hsg, hch⟩ := h
      refine WP.mono (verifySetup_ok hp) fun t ⟨vt, rt, ft, _⟩ => ?_
      rw [e3, e4, e5, e6] at vt
      rw [e6] at ft
      have hs : ∀ r ∈ [(⟨b, 8192⟩ : Region)], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
        rw [List.mem_singleton.mp hr]; exact fun _ h => h
      refine ⟨vt, by rw [rt.sp, hsp], ?_, ?_, ?_⟩
      · rw [bytesAt_ws ft hs vt.pkD (by decide), hpk]
      · rw [bytesAt_ws ft hs vt.sigD (by decide), hsg]
      · rw [bytesAt_ws ft hs vt.chD (by decide), hch]
  have h2 := ctBoth (verifyBody_ct (b := b) (sp := sp) (pk := pk) (sig := sig) (ch := ch) (PK := PK) (SG := SG)
    (CH := CH)) (B := Pin b sp) fun s h => WP.mono (verifyBody_ok h.1) fun t ⟨rt, _, _⟩ =>
      Pin.of_rest ⟨h.1.ctx, h.2.1⟩ rt (by decide)
  exact RelCT.seq h1 (RelCT.seq h2 (ctRegs [.a3] (A := Pin b sp) (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)))

end

end VG.Proof.Ed25519.RISCV64
