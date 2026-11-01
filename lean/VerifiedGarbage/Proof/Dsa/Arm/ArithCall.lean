module

public import VerifiedGarbage.Proof.Dsa.Arm.Arith
import VerifiedGarbage.Proof.Dsa.Arm.PowCall
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-!
# DSA's reductions and products as functions on 32-bit ARM: their calls

Calls of `vg_dsa_mulmod_{n}` and `vg_dsa_reduce_{n}` from code whose working
space is at `r12`, as `PowCall.lean` for `vg_dsa_pow_{n}_{e}`: the context's
bytes are the function's working space, which its contract narrows the call
to, with the reduction's bytes, and `r12` comes back from `r11`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Pow VG.Impl.Dsa.Arm.Arith
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_dp wp_movw op2_reg dpVal)

theorem mulBody_noFrames (n : Nat) : (mulBody n).noFrames = true := by
  simp only [mulBody, Impl.Dsa.Arm.Context.call, Impl.Dsa.Arm.Context.body, contextSetup, ordinaryMul, Dynamic.mul, rowD, digitRowD, mulRowD, csubD, Dynamic.zeros,
    ptrLoop, one, powerTwo, addD, addDigits, Code.noFrames, Bool.and_self]

theorem doubles_noCalls (n k : Nat) : (doubles n k).noCalls = true := by
  unfold doubles
  split <;> simp only [countedDouble, addDigits, csubD, ptrLoop, Code.noCalls, Bool.and_self]

theorem reduceBody_noFrames (n : Nat) : (reduceBody n).noFrames = true := by
  simp only [reduceBody, Impl.Dsa.Arm.Context.light, reduceStream, streamStep, reduceStep, addD, addDigits,
    csubD, Dynamic.zeros, ptrLoop, Code.noFrames, Bool.and_self, Bool.and_true, Bool.true_and]
  exact Code.noFrames_of_noCalls (doubles_noCalls n 8)

/-! ## Products -/

theorem mulCall_ok {s : State} {base : Addr} {size n m : Nat} (hs : Ws s base size) (hz : contextBytes n ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48) (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m)
    (hodd : m % 2 = 1) :
    WP isa (mulCall n) s fun t => Ws t base size ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) * val32 s.mem base (slot n 11) (2 * n) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r11, .lr] s t := by
  unfold mulCall
  refine WP.seq (WP.mono (head_ok n) fun u ⟨h11, h0, h1, R₁, M₁⟩ => ?_)
  have w₁ := hs.of_rest R₁ (by decide)
  refine WP.seq (WP.callCalls (k := mulK n) (mulK_correct hn hn48)
    (entry_pre (e := 1) hs hz hn48 h0 h1 M₁ (by rw [hv]; exact hodd) (by rw [hv]; exact hm1))
    (Covers.right (covers_ctx w₁ hz)) (covers_ctx w₁ hz) (fun v hrd hwr hsp _ P _ post => ?_) (mulBody_noFrames n))
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  simp only [mulK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, b0, M₁, hv] at post
  obtain ⟨V, O⟩ := post
  have v11 : v.gpr .r11 = s.gpr .r12 := by rw [P _ (by decide) (by decide), h11]
  refine wp_mov (op2_reg v .r11) fun t v₂ => WP.block_nil ⟨⟨?_, ?_, hs.nowrap⟩, ?_, ?_, ?_⟩
  · rw [v₂.gpr, v11, hs.wb]
  · rw [v₂.wr, hwr]; exact w₁.wr
  · rw [v₂.mem]; exact V
  · rw [v₂.mem]; exact O
  · refine ⟨fun r hr => ?_, by rw [v₂.rd, hrd, R₁.rd], by rw [v₂.wr, hwr, R₁.wr], by rw [v₂.sp, hsp, R₁.sp]⟩
    by_cases h12 : r = .r12
    · subst h12; rw [v₂.gpr, v11]
    · rw [v₂.other _ h12]
      have hp : r ∈ preserved ∧ r ≠ .lr ∧ r ∉ [.r0, .r1, .r11] := by revert hr h12; cases r <;> decide
      rw [P _ hp.1 hp.2.1, R₁.gpr _ hp.2.2]

theorem mulCall_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n : Nat} (hs₁ : Ws s₁ base size₁)
    (hs₂ : Ws s₂ base size₂) (hz₁ : contextBytes n ≤ size₁) (hz₂ : contextBytes n ≤ size₂)
    (hn : 0 < n) (hn48 : n ≤ 48)
    (ho₁ : val32 s₁.mem base (slot n 0) (2 * n) % 2 = 1) (hm₁ : 1 < val32 s₁.mem base (slot n 0) (2 * n))
    (ho₂ : val32 s₂.mem base (slot n 0) (2 * n) % 2 = 1) (hm₂ : 1 < val32 s₂.mem base (slot n 0) (2 * n)) :
    SameTrace isa (mulCall n) s₁ s₂ := by
  have nothing : ∀ a b : State, VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs []) a b :=
    fun _ _ => VG.Arm.Taint.agree_ofRegs fun _ h => nomatch h
  unfold mulCall head
  refine SameTrace.seq (SameTrace.of_relCT (erased_relCT (τ := VG.Arm.Taint.ofRegs [])
      (σ := VG.Arm.Taint.ofRegs []) (c₀ := .block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide)) (nothing _ _)) (head_ok n) (head_ok n)
    fun u₁ u₂ ⟨_, h0₁, h1₁, R₁, M₁⟩ ⟨_, h0₂, h1₂, R₂, M₂⟩ => ?_
  have w₁ := hs₁.of_rest R₁ (by decide)
  have w₂ := hs₂.of_rest R₂ (by decide)
  refine SameTrace.of_relCT (P := fun a b => a = u₁ ∧ b = u₂) (RelCT.seq
    (RelCT.call (mulK_correct hn hn48) (mulK_ct n hn hn48) [] [⟨base, contextBytes n⟩] ?_)
    ((relCT_of_check (τ := VG.Arm.Taint.ofRegs []) (σ := VG.Arm.Taint.ofRegs []) (h := .block [])
      (by decide)).mono (fun _ _ _ => nothing _ _) fun _ _ _ => trivial)) ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  refine ⟨entry_pre (e := 1) hs₁ hz₁ hn48 h0₁ h1₁ M₁ ho₁ hm₁, entry_pre (e := 1) hs₂ hz₂ hn48 h0₂ h1₂ M₂ ho₂ hm₂,
    ?_, Covers.right (covers_ctx w₁ hz₁), covers_ctx w₁ hz₁, Covers.right (covers_ctx w₂ hz₂), covers_ctx w₂ hz₂⟩
  simp only [mulK, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h0₁, h0₂]
  exact BitVec.eq_of_toNat_eq (by rw [hs₁.wb_toNat, hs₂.wb_toNat])

/-! ## Reductions -/

/-- The bytes' address and length. -/
theorem rpre_ok {s : State} :
    WP isa (.block [.mov .r2 (.reg .r11), .dp .sub .r3 .lr (.reg .r11)]) s fun u =>
      u.gpr .r2 = s.gpr .r11 ∧ u.gpr .r3 = s.gpr .lr - s.gpr .r11 ∧ Rest [.r2, .r3] s u ∧ u.mem = s.mem :=
  wp_mov (op2_reg s .r11) fun u₁ v₁ => wp_dp (op2_reg _ _) fun u₂ v₂ => WP.block_nil
    ⟨by rw [v₂.other _ (by decide), v₁.gpr], by rw [v₂.gpr, dpVal, v₁.other _ (by decide), v₁.other _ (by decide)],
      (v₁.rest (by decide)).trans (v₂.rest (by decide)), by rw [v₂.mem, v₁.mem]⟩

/-- The bytes' address and length, then the arguments. -/
theorem rhead_ok {s : State} (n : Nat) :
    WP isa (.block (([.mov .r2 (.reg .r11), .dp .sub .r3 .lr (.reg .r11)] : List Instr) ++ head n)) s fun u =>
      u.gpr .r2 = s.gpr .r11 ∧ u.gpr .r3 = s.gpr .lr - s.gpr .r11 ∧ u.gpr .r11 = s.gpr .r12 ∧
        u.gpr .r0 = s.gpr .r12 ∧ u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32 ∧
        Rest [.r0, .r1, .r2, .r3, .r11] s u ∧ u.mem = s.mem :=
  VG.Proof.X25519.Arm.WP.append rpre_ok fun u ⟨h2, h3, R, M⟩ => WP.mono (head_ok n) fun t ⟨h11, h0, h1, R', M'⟩ =>
    ⟨by rw [R'.gpr _ (by decide), h2], by rw [R'.gpr _ (by decide), h3],
      by rw [h11, R.gpr _ (by decide)], by rw [h0, R.gpr _ (by decide)], h1,
      (R.mono (by decide)).trans (R'.mono (by decide)), M'.trans M⟩

/-- On entry to the function, its precondition, narrowed to the context and
the bytes. -/
theorem rentry_pre {s u : State} {base : Addr} {size n len : Nat} {p : BitVec 32} (hs : Ws s base size)
    (hz : contextBytes n ≤ size) (hn48 : n ≤ 48) (h0 : u.gpr .r0 = s.gpr .r12)
    (h1 : u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32) (h2 : u.gpr .r2 = p)
    (h3 : (u.gpr .r3).toNat = len) (hfit : p.toNat + len ≤ 2 ^ 32)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨base, contextBytes n⟩)
    (hm : u.mem = s.mem) (hodd : val32 s.mem base (slot n 0) (2 * n) % 2 = 1)
    (hm255 : 255 < val32 s.mem base (slot n 0) (2 * n)) :
    (reduceK n).pre (u.callEntry.withRegions [⟨State.addr p, len⟩] [⟨base, contextBytes n⟩]) := by
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by
    rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  have l1 : (u.callEntry.gpr .r1).toNat * 8 = contextBytes n := by
    rw [State.callEntry_gpr _ (by decide), h1]; exact words_eq hn48
  have e2 : u.callEntry.gpr .r2 = p := by rw [State.callEntry_gpr _ (by decide), h2]
  have e3 : (u.callEntry.gpr .r3).toNat = len := by rw [State.callEntry_gpr _ (by decide), h3]
  simp only [reduceK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, b0, l1, e2, e3, hm]
  refine ⟨trivial, trivial, ?_, hfit, Nat.le_refl _, hd.symm, hodd, hm255⟩
  rw [State.callEntry_gpr _ (by decide), h0, hs.wb_toNat]
  have := hs.nowrap
  omega

theorem reduceCall_ok {s : State} {base : Addr} {size n m len : Nat} {p : BitVec 32} (hs : Ws s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) (hv : val32 s.mem base (slot n 0) (2 * n) = m)
    (hm : 255 < m) (hodd : m % 2 = 1) (h11 : s.gpr .r11 = p) (hlr : s.gpr .lr = p + BitVec.ofNat 32 len)
    (hfit : p.toNat + len ≤ 2 ^ 32) (llt : len < 2 ^ 32) (hr : InRegions (s.rd ++ s.wr) (State.addr p) len)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨base, contextBytes n⟩) :
    WP isa (reduceCall n) s fun t => Ws t base size ∧
      val32 t.mem base (slot n 9) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) len) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r11, .lr] s t := by
  have l3 : (s.gpr .lr - s.gpr .r11).toNat = len := by
    rw [hlr, h11, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt llt]
  unfold reduceCall
  refine WP.seq (WP.mono (rhead_ok n) fun u ⟨h2, h3, h11', h0, h1, R₁, M₁⟩ => ?_)
  have w₁ := hs.of_rest R₁ (by decide)
  refine WP.seq (WP.callCalls (k := reduceK n) (reduceK_correct hn hn48)
    (rentry_pre hs hz hn48 h0 h1 (h2.trans h11) (by rw [h3, l3]) hfit hd M₁ (by rw [hv]; exact hodd)
      (by rw [hv]; exact hm))
    (Covers.append_left (Covers.one (by rw [R₁.rd, R₁.wr]; exact hr)) (Covers.right (covers_ctx w₁ hz)))
    (covers_ctx w₁ hz) (fun v hrd hwr hsp _ P _ post => ?_) (reduceBody_noFrames n))
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  have e2 : u.callEntry.gpr .r2 = p := by rw [State.callEntry_gpr _ (by decide), h2, h11]
  have e3 : (u.callEntry.gpr .r3).toNat = len := by rw [State.callEntry_gpr _ (by decide), h3, l3]
  simp only [reduceK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, b0, e2, e3, M₁, hv]
    at post
  obtain ⟨V, O⟩ := post
  have v11 : v.gpr .r11 = s.gpr .r12 := by rw [P _ (by decide) (by decide), h11']
  refine wp_mov (op2_reg v .r11) fun t v₂ => WP.block_nil ⟨⟨?_, ?_, hs.nowrap⟩, ?_, ?_, ?_⟩
  · rw [v₂.gpr, v11, hs.wb]
  · rw [v₂.wr, hwr]; exact w₁.wr
  · rw [v₂.mem]; exact V
  · rw [v₂.mem]; exact O
  · refine ⟨fun r hr => ?_, by rw [v₂.rd, hrd, R₁.rd], by rw [v₂.wr, hwr, R₁.wr], by rw [v₂.sp, hsp, R₁.sp]⟩
    by_cases h12 : r = .r12
    · subst h12; rw [v₂.gpr, v11]
    · rw [v₂.other _ h12]
      have hp : r ∈ preserved ∧ r ≠ .lr ∧ r ∉ [.r0, .r1, .r2, .r3, .r11] := by
        revert hr h12; cases r <;> decide
      rw [P _ hp.1 hp.2.1, R₁.gpr _ hp.2.2]

theorem reduceCall_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n len : Nat} {p : BitVec 32}
    (hs₁ : Ws s₁ base size₁) (hs₂ : Ws s₂ base size₂) (hz₁ : contextBytes n ≤ size₁)
    (hz₂ : contextBytes n ≤ size₂) (hn : 0 < n) (hn48 : n ≤ 48)
    (ho₁ : val32 s₁.mem base (slot n 0) (2 * n) % 2 = 1) (hm₁ : 255 < val32 s₁.mem base (slot n 0) (2 * n))
    (ho₂ : val32 s₂.mem base (slot n 0) (2 * n) % 2 = 1) (hm₂ : 255 < val32 s₂.mem base (slot n 0) (2 * n))
    (a₁ : s₁.gpr .r11 = p) (l₁ : s₁.gpr .lr = p + BitVec.ofNat 32 len)
    (a₂ : s₂.gpr .r11 = p) (l₂ : s₂.gpr .lr = p + BitVec.ofNat 32 len)
    (hfit : p.toNat + len ≤ 2 ^ 32) (llt : len < 2 ^ 32) (hr₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr p) len)
    (hr₂ : InRegions (s₂.rd ++ s₂.wr) (State.addr p) len)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨base, contextBytes n⟩) :
    SameTrace isa (reduceCall n) s₁ s₂ := by
  have nothing : ∀ a b : State, VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs []) a b :=
    fun _ _ => VG.Arm.Taint.agree_ofRegs fun _ h => nomatch h
  have l3 : ∀ {s : State}, s.gpr .r11 = p → s.gpr .lr = p + BitVec.ofNat 32 len →
      (s.gpr .lr - s.gpr .r11).toNat = len := fun h11 hlr => by
    rw [hlr, h11, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt llt]
  unfold reduceCall head
  refine SameTrace.seq (SameTrace.of_relCT (erased_relCT (τ := VG.Arm.Taint.ofRegs [])
      (σ := VG.Arm.Taint.ofRegs [])
      (c₀ := .block [.mov .r2 (.reg .r11), .dp .sub .r3 .lr (.reg .r11), .mov .r11 (.reg .r12),
        .mov .r0 (.reg .r12), .movw .r1 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide)) (nothing _ _)) (rhead_ok n) (rhead_ok n)
    fun u₁ u₂ ⟨h2₁, h3₁, _, h0₁, h1₁, R₁, M₁⟩ ⟨h2₂, h3₂, _, h0₂, h1₂, R₂, M₂⟩ => ?_
  have w₁ := hs₁.of_rest R₁ (by decide)
  have w₂ := hs₂.of_rest R₂ (by decide)
  refine SameTrace.of_relCT (P := fun a b => a = u₁ ∧ b = u₂) (RelCT.seq
    (RelCT.call (reduceK_correct hn hn48) (reduceK_ct n hn hn48) [⟨State.addr p, len⟩]
      [⟨base, contextBytes n⟩] ?_)
    ((relCT_of_check (τ := VG.Arm.Taint.ofRegs []) (σ := VG.Arm.Taint.ofRegs []) (h := .block [])
      (by decide)).mono (fun _ _ _ => nothing _ _) fun _ _ _ => trivial)) ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  refine ⟨rentry_pre hs₁ hz₁ hn48 h0₁ h1₁ (h2₁.trans a₁) (by rw [h3₁, l3 a₁ l₁]) hfit hd M₁ ho₁ hm₁,
    rentry_pre hs₂ hz₂ hn48 h0₂ h1₂ (h2₂.trans a₂) (by rw [h3₂, l3 a₂ l₂]) hfit hd M₂ ho₂ hm₂, ?_,
    Covers.append_left (Covers.one (by rw [R₁.rd, R₁.wr]; exact hr₁)) (Covers.right (covers_ctx w₁ hz₁)),
    covers_ctx w₁ hz₁,
    Covers.append_left (Covers.one (by rw [R₂.rd, R₂.wr]; exact hr₂)) (Covers.right (covers_ctx w₂ hz₂)),
    covers_ctx w₂ hz₂⟩
  simp only [reduceK, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    h0₁, h0₂, h2₁, h2₂, h3₁, h3₂, a₁, a₂, l₁, l₂]
  exact ⟨BitVec.eq_of_toNat_eq (by rw [hs₁.wb_toNat, hs₂.wb_toNat]), rfl, rfl⟩

end VG.Proof.Dsa.Arm.Pow
