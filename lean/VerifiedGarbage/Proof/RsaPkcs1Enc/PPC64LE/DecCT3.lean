module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCT2
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecIrprf
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCT2
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecIrprf
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: constant time of IRPRF

A block of IRPRF (`prfBody_ct`) keeps `Post` and the counters in their
slots (`SL`), the blocks by the taint analysis and the calls the same in
both runs; the loops (`clLoop_ct`, `amLoop_ct`) run the same number of
blocks in both runs, which the public `k` fixes.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

/-- The counter `i` and the number of blocks `nb s` in their slots. -/
def SL (i : Nat) (nb : State → BitVec 64) (s u : State) : Prop :=
  sl s u oI = BitVec.ofNat 64 i ∧ sl s u oNB = nb s

theorem SL.mem {i : Nat} {nb : State → BitVec 64} {s u v : State} (h : SL i nb s u) (hm : v.mem = u.mem) :
    SL i nb s v := by
  unfold SL sl at *; rw [hm]; exact h

/-- The counters stay through a call working in `scratch`. -/
theorem SL.call {i : Nat} {nb : State → BitVec 64} {s u v : State} (hd : DPre s) (h : SL i nb s u)
    {ws : List Region} {n : Nat} (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes)
    (hf : Frame (ws ++ [below (fb s) n]) u.mem v.mem) (hs : ∀ r ∈ ws, Region.Sub r (SC s)) : SL i nb s v :=
  ⟨(slot_call hd hn hf hs (by decide)).trans h.1, (slot_call hd hn hf hs (by decide)).trans h.2⟩

/-- The counters stay through a write in `scratch`. -/
theorem SL.sc {i : Nat} {nb : State → BitVec 64} {s u v : State} (hd : DPre s) (h : SL i nb s u)
    {ws : List Region} (hf : Frame ws u.mem v.mem) (hs : ∀ r ∈ ws, Region.Sub r (SC s)) : SL i nb s v := by
  have hf' : Frame (ws ++ [below (fb s) 0]) u.mem v.mem :=
    hf.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
  exact h.call hd (by decide) hf' hs

/-! ## A block -/

section
variable {e : Env}

/-- The facts at a block's start. -/
def B0 (i : Nat) (nb : State → BitVec 64) (s u : State) : Prop := PP s u ∧ SL i nb s u

theorem b0_sp {i : Nat} {nb : State → BitVec 64} {a b : State} (ha : B0 i nb e.s₁ a) (hb : B0 i nb e.s₂ b) :
    a.sp = b.sp := pp_sp ha.1 hb.1

/-- One block of IRPRF, with the label `label`, the bit length's code `len`,
to `scratch + dst + 32 i`, the blocks left from `C`. -/
theorem prfBody_ct {label : List Nat} {len count : List Instr} {dst i : Nat} {nb C : State → BitVec 64}
    (hi : i < 256) (hd1 : 1136 ≤ dst) (hd2 : dst + 32 * i + 32 ≤ scrBytes) (hdst : dst < 2 ^ 15)
    (hn : label.length + 4 ≤ 16)
    {hc₁ : VG.Taint.Hint T} (ht₁ : (vectorTaint.check (ofRegs [.r9, .r11, .r8]) (.block (msgBytes label len)) hc₁).isSome = true)
    (hmsg : ∀ s u, DPre s → PP s u → u.gpr .r9 = scA s sMsg → u.gpr .r11 = BitVec.ofNat 64 i →
      u.gpr .r8 = s.gpr .r7 → WP isa (.block (msgBytes label len)) u fun w =>
        Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧ VG.Proof.Bignum.PPC64LE.Keep [.r10] u w)
    {hc₂ : VG.Taint.Hint T} (ht₂ : (vectorTaint.check (ofRegs []) (.block (incr count)) hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint T} (ht₃ : (vectorTaint.check (ofRegs []) (.block (prfUpdArgs (label.length + 4))) hc₃).isSome = true)
    {hc₄ : VG.Taint.Hint T}
    (ht₄ : (vectorTaint.check (ofRegs []) (.block (prfFinArgs (label.length + 4) dst)) hc₄).isSome = true)
    (hcount : ∀ s u, DPre s → PP s u → sl s u oNB = nb s → WP isa (.block (incr count)) u fun w =>
      (w.mem = u.mem.writeW (fb s + BitVec.ofNat 64 oI) (sl s u oI + 1) ∧
        w.gpr .r9 = C s - (sl s u oI + 1)) ∧ VG.Proof.Bignum.PPC64LE.Keep [.r12, .r11, .r9] u w) :
    RelCT isa (Rel e (B0 i nb)) (prfBody label len dst count)
      (Rel e fun s u => PP s u ∧ SL (i + 1) nb s u ∧ u.gpr .r9 = C s - BitVec.ofNat 64 (i + 1)) := by
  have e₁ : H.S = 96 := rfl
  have e₂ : H.W = 160 := rfl
  have e₃ : H.D = 32 := rfl
  unfold prfBody
  -- The head.
  refine RelCT.seq
    (rel_step (P' := fun s u => B0 i nb s u ∧ u.gpr .r9 = scA s sMsg ∧
      u.gpr .r11 = BitVec.ofNat 64 i ∧ u.gpr .r8 = s.gpr .r7) [] (by taint_decide) (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
      fun s u _ ⟨hu, hs⟩ => WP.mono (pp_block hu [.r12, .r9, .r11, .r8] fun _ _ hc => prfHead_ok hc)
        fun v ⟨hv, vm, x9, x11, x8⟩ => ⟨⟨hv, hs.mem vm⟩, x9, by rw [x11, hs.1], x8⟩) ?_
  -- The message.
  refine RelCT.seq
    (rel_step (P' := B0 i nb) [.r9, .r11, .r8] ht₁ (fun a b ⟨ha, a9, a11, a8⟩ ⟨hb, b9, b11, b8⟩ => ⟨b0_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a9, b9, e.scA_eq]
      · rw [a11, b11]
      · rw [a8, b8, e.r]⟩)
      fun s u h ⟨⟨⟨R, EM, hu⟩, hs⟩, x9, x11, x8⟩ => WP.mono (hmsg s u h ⟨R, EM, hu⟩ x9 x11 x8)
        fun v ⟨F, kv⟩ => ⟨⟨R, EM, hu.step h kv.rd kv.wr kv.sp (fun r hr => kv.gpr r (by revert r; decide)) F
          fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (scSub (by decide))⟩,
          hs.sc h F fun r hr => by rw [List.mem_singleton.mp hr]; exact scSub (by decide)⟩) ?_
  -- HMAC's `init` with `KDK`.
  refine RelCT.seq
    (rel_step (P' := fun s u => B0 i nb s u ∧ PMI sKDK s u) [] (by taint_decide) (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
      fun s u _ ⟨hu, hs⟩ => WP.mono (pp_block hu [.r12, .r3, .r4, .r5, .r6, .r7] fun _ _ hc =>
        macInitArgs_ok hc (key := sKDK) (by decide))
        fun v ⟨hv, vm, x⟩ => ⟨⟨hv, hs.mem vm⟩, hv, x⟩) ?_
  refine RelCT.seq
    (rel_post (P' := B0 i nb) (macInit_rel fun a b ⟨⟨_, ha⟩, _, hb⟩ => pmi_agree ha hb)
      fun s u h ⟨⟨_, hs⟩, ⟨_, _, hu⟩, u3, u4, u5, u6, u7⟩ => macInit_call h hu (by decide) (by decide) u3 u4 u5 u6 u7
        fun v hv _ _ hf => ⟨⟨_, _, hv⟩, hs.call h (by decide) hf fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact scSub (by decide)⟩) ?_
  -- `update` with the message.
  refine RelCT.seq
    (rel_step (P' := fun s u => B0 i nb s u ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = BitVec.ofNat 64 64 ∧
      u.gpr .r5 = scA s sMsg ∧ u.gpr .r6 = BitVec.ofNat 64 (label.length + 4) ∧ u.gpr .r7 = scA s sWork)
      [] ht₃ (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
      fun s u _ ⟨hu, hs⟩ => WP.mono (pp_block hu [.r12, .r3, .r4, .r5, .r6, .r7] fun _ _ hc =>
        prfUpdArgs_ok hc (n := label.length + 4) (by omega))
        fun v ⟨hv, vm, x⟩ => ⟨⟨hv, hs.mem vm⟩, x⟩) ?_
  refine RelCT.seq
    (rel_post (P' := B0 i nb) (upd_rel fun a b ⟨⟨ha, a3, a4, a5, a6, a7⟩, hb, b3, b4, b5, b6, b7⟩ => ⟨b0_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a3, b3, e.scA_eq]
      · rw [a4, b4]
      · rw [a5, b5, e.scA_eq]
      · rw [a6, b6]
      · rw [a7, b7, e.scA_eq]⟩)
      fun s u h ⟨⟨⟨_, _, hu⟩, hs⟩, u3, _, u5, u6, u7⟩ =>
        upd_call h hu (len := label.length + 4) u3 u5 (by rw [u6, BitVec.toNat_ofNat]; omega) u7
          (scD h (.inr (by decide)) (by unfold sMsg scrBytes; omega) (by decide))
          (scD h (.inr (by decide)) (by unfold sMsg scrBytes; omega) (by decide))
          (lowD h (by decide) (by unfold sMsg scrBytes; omega)) (scCovR h hu.wr (by unfold sMsg scrBytes; omega))
          fun v hv _ hf => ⟨⟨_, _, hv⟩, hs.call h (by decide) hf fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl <;> exact scSub (by decide)⟩) ?_
  -- HMAC's `finalize` to the block.
  refine RelCT.seq
    (rel_step (P' := fun s u => B0 i nb s u ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = scA s sOuter ∧
      u.gpr .r5 = BitVec.ofNat 64 (64 + (label.length + 4)) ∧ u.gpr .r6 = scA s (dst + 32 * i) ∧
      u.gpr .r7 = scA s sWork) [] ht₄ (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
      fun s u _ ⟨hu, hs⟩ => WP.mono (pp_block hu [.r12, .r3, .r4, .r5, .r6, .r10, .r7] fun _ _ hc =>
        prfFinArgs_ok hc (n := label.length + 4) (dst := dst) (by omega) hdst)
        fun v ⟨hv, vm, x3, x4, x5, x6, x7⟩ => ⟨⟨hv, hs.mem vm⟩, x3, x4, x5, by rw [x6, hs.1, shl5], x7⟩) ?_
  refine RelCT.seq
    (rel_post (P' := B0 i nb) (macFin_rel fun a b ⟨⟨ha, a3, a4, a5, a6, a7⟩, hb, b3, b4, b5, b6, b7⟩ => ⟨b0_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a3, b3, e.scA_eq]
      · rw [a4, b4, e.scA_eq]
      · rw [a5, b5]
      · rw [a6, b6, e.scA_eq]
      · rw [a7, b7, e.scA_eq]⟩)
      fun s u h ⟨⟨⟨_, _, hu⟩, hs⟩, u3, u4, _, u6, u7⟩ =>
        macFin_call h hu (o := dst + 32 * i) (by omega) hd2 u3 u4 u6 u7
          fun v hv _ hf => ⟨⟨_, _, hv⟩, hs.call h (by decide) hf fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact scSub (by decide)
            · exact scSub hd2
            · exact scSub (by decide)⟩) ?_
  -- The counter.
  refine rel_step [] ht₂ (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
    fun s u h ⟨⟨R, EM, hu⟩, hs⟩ => WP.mono (hcount s u h ⟨R, EM, hu⟩ hs.2) fun w ⟨⟨wm, w9⟩, kw⟩ => ?_
  have Fw : Frame [⟨fb s + BitVec.ofNat 64 oI, 8⟩] u.mem w.mem := by
    rw [wm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have one : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  refine ⟨⟨R, EM, hu.step h kw.rd kw.wr kw.sp (fun r hr => kw.gpr r (by revert r; decide)) Fw fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨oI, Nat.le_refl _, show oI + 8 ≤ oLr by decide, rfl⟩)⟩,
    ⟨?_, ?_⟩, by rw [w9, hs.1, one]⟩
  · show w.mem.readW _ 64 = _
    rw [wm, Mem.readW_writeW_self64, hs.1, one]
  · show w.mem.readW _ 64 = _
    rw [wm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact hs.2

/-! ## The loops -/

/-- The loop's invariant, `n` blocks before its end. -/
def LI (N : State → Nat) (nb : State → BitVec 64) (n : Nat) (s u : State) : Prop :=
  n ≤ N s ∧ 0 < n ∧ B0 (N s - n) nb s u

theorem prfLoop_ct {label : List Nat} {len count : List Instr} {dst : Nat} {N : State → Nat}
    {nb C : State → BitVec 64} (hN : N e.s₁ = N e.s₂) (hN0 : 0 < N e.s₁) (hN256 : N e.s₁ ≤ 256)
    (hd1 : 1136 ≤ dst) (hd2 : dst + 32 * N e.s₁ ≤ scrBytes) (hdst : dst < 2 ^ 15) (hn : label.length + 4 ≤ 16)
    (hCe : C e.s₁ = C e.s₂) (hCv : ∀ i < N e.s₁, C e.s₁ - BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (N e.s₁ - (i + 1)))
    {hc₁ : VG.Taint.Hint T} (ht₁ : (vectorTaint.check (ofRegs [.r9, .r11, .r8]) (.block (msgBytes label len)) hc₁).isSome = true)
    (hmsg : ∀ i < 256, ∀ s u, DPre s → PP s u → u.gpr .r9 = scA s sMsg → u.gpr .r11 = BitVec.ofNat 64 i →
      u.gpr .r8 = s.gpr .r7 → WP isa (.block (msgBytes label len)) u fun w =>
        Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧ VG.Proof.Bignum.PPC64LE.Keep [.r10] u w)
    {hc₂ : VG.Taint.Hint T} (ht₂ : (vectorTaint.check (ofRegs []) (.block (incr count)) hc₂).isSome = true)
    (hcount : ∀ s u, DPre s → PP s u → sl s u oNB = nb s → WP isa (.block (incr count)) u fun w =>
      (w.mem = u.mem.writeW (fb s + BitVec.ofNat 64 oI) (sl s u oI + 1) ∧
        w.gpr .r9 = C s - (sl s u oI + 1)) ∧ VG.Proof.Bignum.PPC64LE.Keep [.r12, .r11, .r9] u w)
    {hc₃ : VG.Taint.Hint T} (ht₃ : (vectorTaint.check (ofRegs []) (.block (prfUpdArgs (label.length + 4))) hc₃).isSome = true)
    {hc₄ : VG.Taint.Hint T}
    (ht₄ : (vectorTaint.check (ofRegs []) (.block (prfFinArgs (label.length + 4) dst)) hc₄).isSome = true) :
    RelCT isa (Rel e (B0 0 nb)) (.loop (prfBody label len dst count) (.nonzero .d .r9))
      (Rel e fun s u => B0 (N s) nb s u) := by
  have step : ∀ n, RelCT isa (Rel e (LI N nb n)) (prfBody label len dst count) fun a b =>
      isa.eval (.nonzero .d .r9) a = isa.eval (.nonzero .d .r9) b ∧
      (isa.eval (.nonzero .d .r9) a = some false → Rel e (fun s u => B0 (N s) nb s u) a b) ∧
      (isa.eval (.nonzero .d .r9) a = some true → ∃ m < n, Rel e (LI N nb m) a b) := by
    intro n
    by_cases hn' : 0 < n ∧ n ≤ N e.s₁
    · have hi : N e.s₁ - n < N e.s₁ := by omega
      refine (prfBody_ct (e := e) (i := N e.s₁ - n) (C := C) (by omega) hd1 (by omega) hdst hn ht₁
        (hmsg _ (by omega)) ht₂ ht₃ ht₄ hcount).mono
        (fun a b ⟨⟨_, _, ha⟩, _, _, hb⟩ => ⟨ha, by rw [hN]; exact hb⟩) fun a b ⟨⟨ha, sa, a9⟩, hb, sb, b9⟩ => ?_
      have ev : ∀ x : State, isa.eval (.nonzero .d .r9) x = some (x.gpr .r9 != 0) :=
        fun x => VG.Proof.Bignum.PPC64LE.eval_nonzero x .r9
      have a9' : a.gpr .r9 = BitVec.ofNat 64 (N e.s₁ - (N e.s₁ - n + 1)) := by rw [a9, hCv _ hi]
      have b9' : b.gpr .r9 = BitVec.ofNat 64 (N e.s₁ - (N e.s₁ - n + 1)) := by rw [b9, ← hCe, hCv _ hi]
      have hz : (BitVec.ofNat 64 (N e.s₁ - (N e.s₁ - n + 1)) != 0) = decide (n ≠ 1) := by
        rw [VG.Proof.Bignum.PPC64LE.ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact decide_eq_decide.mpr (by omega)
      refine ⟨by rw [ev, ev, a9', b9'], fun hf => ?_, fun ht => ?_⟩
      · rw [ev, a9', hz] at hf
        have : n = 1 := by simpa using hf
        subst this
        exact ⟨⟨ha, by rw [show N e.s₁ - 1 + 1 = N e.s₁ by omega] at sa; exact sa⟩,
          ⟨hb, by rw [show N e.s₁ - 1 + 1 = N e.s₁ by omega, hN] at sb; exact sb⟩⟩
      · rw [ev, a9', hz] at ht
        have : n ≠ 1 := by simpa using ht
        refine ⟨n - 1, by omega, ⟨by omega, by omega, ha, ?_⟩, ⟨by rw [← hN]; omega, by omega, hb, ?_⟩⟩
        · rw [show N e.s₁ - (n - 1) = N e.s₁ - n + 1 by omega]; exact sa
        · rw [← hN, show N e.s₁ - (n - 1) = N e.s₁ - n + 1 by omega]; exact sb
    · exact RelCT.of_false fun a b ⟨⟨h₁, h₂, _⟩, _⟩ => hn' ⟨h₂, h₁⟩
  exact (RelCT.loop (Q := Rel e fun s u => B0 (N s) nb s u) _ step (N e.s₁)).mono
    (fun a b ⟨ha, hb⟩ => ⟨⟨Nat.le_refl _, hN0, by rw [Nat.sub_self]; exact ha⟩,
      ⟨by rw [← hN], hN0, by rw [← hN, Nat.sub_self]; exact hb⟩⟩) fun _ _ h => h

/-- The number of `AM`'s blocks. -/
abbrev nbOf (s : State) : BitVec 64 := BitVec.ofNat 64 (((s.gpr .r7).toNat + 31) / 32)

theorem clLoop_ct : RelCT isa (Rel e PP) clLoop (Rel e fun s u => B0 8 nbOf s u) := by
  have hk₁ := e.h₁.k2
  have hk₁' := e.h₁.k1
  unfold clLoop
  refine RelCT.seq (rel_step (P' := B0 0 nbOf) [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha hb, fun _ h => nomatch h⟩)
    fun s u h ⟨R, EM, hu⟩ => WP.mono (clStart_ok h hu) fun v ⟨hv, c, n, _⟩ => ⟨⟨_, _, hv⟩, c, n⟩) ?_
  exact prfLoop_ct (N := fun _ => 8) rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl (fun i hi => Offset.ofNat_sub_ofNat (by omega)) (by taint_decide)
    (fun i hi s u h hu x9 x11 _ => WP.mono (msgCL_ok x9 x11 hi (let ⟨_, _, hu⟩ := hu; hu.msgW h))
      fun w ⟨⟨F, _⟩, k⟩ => ⟨F, k⟩)
    (by taint_decide) (fun s u _ ⟨_, _, hu⟩ _ => incrCL_ok hu) (by taint_decide) (by taint_decide)

theorem amLoop_ct : RelCT isa (Rel e fun s u => B0 8 nbOf s u) amLoop (Rel e PP) := by
  have hk₁ := e.h₁.k2
  have hk₁' := e.h₁.k1
  unfold amLoop
  refine RelCT.seq (rel_step (P' := B0 0 nbOf) [] (by taint_decide)
    (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
    fun s u h ⟨⟨R, EM, hu⟩, _, hnb⟩ => WP.mono (amStart_ok h hu hnb) fun v ⟨hv, c, n, _⟩ => ⟨⟨_, _, hv⟩, c, n⟩) ?_
  refine rel_mono (prfLoop_ct (N := fun s => ((s.gpr .r7).toNat + 31) / 32) (C := nbOf) (by rw [e.r]) (by omega)
    (by omega) (by decide) (by unfold sAM scrBytes; omega) (by decide) (by decide)
    (by show nbOf e.s₁ = nbOf e.s₂; rw [nbOf, nbOf, e.r]) (fun i hi => Offset.ofNat_sub_ofNat (by omega))
    (by taint_decide)
    (fun i hi s u h hu x9 x11 x8 => WP.mono (msgAM_ok x9 x11 x8 hi (DPre.k2 h) (let ⟨_, _, hu⟩ := hu; hu.msgW h))
      fun w ⟨⟨F, _⟩, k⟩ => ⟨F, k⟩)
    (by taint_decide) (fun s u _ ⟨_, _, hu⟩ hnb => WP.mono (incrAM_ok hu) fun w ⟨⟨a, b⟩, c⟩ => ⟨⟨a, by rw [b, hnb]⟩, c⟩)
    (by taint_decide) (by taint_decide)) fun _ _ h => h.1

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
