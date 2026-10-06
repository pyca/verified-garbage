import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCT2

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: constant time, `CL` and `AM`

A block of IRPRF (`prfBody_tr`) from two runs with the same counter, whose
slot fixes the block's address, and the loops of blocks (`prfLoop_tr`),
whose counters agree: `clLoop_ct`, `amLoop_ct`.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

variable {v : Compress}

/-- A loop counting down in `cr` from `n`, whose runs agree on `P k` after `k` iterations. -/
theorem count_ct {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (P : Nat → State → State → Prop)
    (hstep : ∀ k < n, RelCT isa (P k) body fun a b =>
      P (k + 1) a b ∧ (a.gpr cr != 0) = decide (k + 1 ≠ n) ∧ (b.gpr cr != 0) = decide (k + 1 ≠ n)) :
    RelCT isa (P 0) (.loop body (.nonzero .x cr)) (P n) := by
  refine (RelCT.loop (fun m a b => ∃ k, k < n ∧ m = n - k ∧ P k a b) (fun m => RelCT.exists_ fun k => ?_) n).mono
    (fun a b h => ⟨0, hn, rfl, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hk, hm, hp⟩ e₁ e₂
  obtain ⟨ht, hq, c₁, c₂⟩ := hstep k hk _ _ _ _ _ _ hp e₁ e₂
  refine ⟨ht, by rw [Bytes.eval_nonzero, Bytes.eval_nonzero, c₁, c₂], fun h => ?_, fun h => ?_⟩
  · rw [Bytes.eval_nonzero, c₁] at h
    have : k + 1 = n := by simpa using h
    exact this ▸ hq
  · rw [Bytes.eval_nonzero, c₁] at h
    have : k + 1 ≠ n := by simpa using h
    exact ⟨n - (k + 1), by omega, k + 1, by omega, rfl, hq⟩

/-- The counter `i` and the number of blocks `nbv` in their slots. -/
def Ctr (L : Lay) (i : Nat) (nbv : BitVec 64) (t : State) : Prop :=
  slot t L.Q oI = BitVec.ofNat 64 i ∧ slot t L.Q oNB = nbv

theorem ctr_slots (L : Lay) (i : Nat) (nbv : BitVec 64) : SlotsPred L (Ctr L i nbv) := fun _ _ ⟨a, b⟩ h =>
  ⟨(h oI (Nat.le_refl _) (by decide)).trans a, (h oNB (by decide) (by decide)).trans b⟩

/-- The registers `prfHead` sets. -/
def XH (L : Lay) (i : Nat) (t : State) : Prop :=
  t.gpr .x9 = scA L sMsg ∧ t.gpr .x11 = BitVec.ofNat 64 i ∧ t.gpr .x12 = L.k

theorem prfBody_tr {S : Nat} (hS : 15 ≤ S) (e : Env) {label : List Nat} {len count : List Instr} {dst i : Nat}
    {nbv C : BitVec 64} (hi : i < 256) (hd1 : 1040 ≤ dst) (hd2 : dst + 32 * i + 32 ≤ scrBytes) (hdst : dst < 4096)
    (hn : label.length + 4 ≤ 16) {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.AArch64.Taint.T}
    (tm : (taint.check (Taint.ofRegs [.x9]) (.block (msgBytes label len)) h₁).isSome = true)
    (tu : (taint.check (Taint.ofRegs []) (.block (prfUpdArgs (label.length + 4))) h₂).isSome = true)
    (tf : (taint.check (Taint.ofRegs []) (.block (prfFinArgs (label.length + 4) dst)) h₃).isSome = true)
    (tc : (taint.check (Taint.ofRegs []) (.block (incr count)) h₄).isSome = true)
    (hmsg : e.L.Ok → ∀ g vv m₀ R EM (u : State), Post e.L g vv m₀ R EM u → XH e.L i u →
      WP isa (.block (msgBytes label len)) u fun w => SameR u w ∧ Frame [⟨scA e.L sMsg, 16⟩] u.mem w.mem)
    (hcount : ∀ g vv m₀ R EM (u : State), Post e.L g vv m₀ R EM u → slot u e.L.Q oNB = nbv →
      WP isa (.block (incr count)) u fun w => SameR u w ∧
        w.mem = u.mem.writeW (e.L.Q + BitVec.ofNat 64 oI) (slot u e.L.Q oI + 1) ∧
        w.gpr .x12 = C - (slot u e.L.Q oI + 1)) :
    RelCT isa (PW S e (Ctr e.L i nbv)) (prfBody (HH v) label len dst count)
      (PW S e fun t => Ctr e.L (i + 1) nbv t ∧ t.gpr .x12 = C - BitVec.ofNat 64 (i + 1)) := by
  have hG := ctr_slots e.L i nbv
  have nil : ∀ {X : State → Prop} (a b : State), X a → X b → ∀ r ∈ ([] : List Reg), a.gpr r = b.gpr r :=
    fun _ _ _ _ _ h => absurd h List.not_mem_nil
  -- The message.
  refine (pw_blk (X' := fun t => Ctr e.L i nbv t ∧ XH e.L i t) [] (by taint_decide) nil
    fun g vv m₀ R EM t _ _ hc hx => WP.mono (prfHead_ok hc.ctx.sp hc.slots) fun u ⟨hs, x9, x11, x12⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, hG t u hx fun _ _ _ => by rw [hs.mem], by simp only [x9, hc.ctx.kept.scr],
        by rw [x11, hx.1], by simp only [x12, hc.ctx.kept.k]⟩).seq ?_
  refine (pw_blk (X' := Ctr e.L i nbv) [.x9] tm (fun a b xa xb r hr => by
      rw [List.mem_singleton.mp hr]; exact xa.2.1.trans xb.2.1.symm)
    fun g vv m₀ R EM t hL _ hc ⟨hx, xh⟩ => WP.mono (hmsg hL _ _ _ _ _ t hc xh) fun w ⟨R₂, F₂⟩ =>
      ⟨⟨R, EM, hc.step hL R₂.rd R₂.wr R₂.sp (fun r _ => by rw [R₂.v]) (fun r hr _ => R₂.cs r hr) F₂
        fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (scSub (by decide))⟩,
      hG t w hx fun d _ hd => F₂.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact hL.stk_buf (by unfold frameBytes at hd; omega) (.inr (.inr (sub_trans (scSub (by decide))
          hL.sc_sub)))) (by decide)⟩).seq ?_
  -- HMAC's `init` with `KDK`.
  refine (macArgs_pw hG sKDK (by decide) (by taint_decide)).seq ((hinit_pw (v := v) hS hG (key := sKDK)
    (by decide) (by decide)).seq ?_)
  -- `update` with the message.
  refine (pw_blk (X' := fun t => Ctr e.L i nbv t ∧ XUp (scA e.L sMsg) (label.length + 4) e.L t) [] tu nil
    fun g vv m₀ R EM t _ _ hc hx => WP.mono (prfUpdArgs_ok hc.ctx.sp hc.slots (n := label.length + 4)
      (by omega)) fun u ⟨hs, y0, y1, y2, y3, y4⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, hG t u hx fun _ _ _ => by rw [hs.mem], by simp only [y0, hc.ctx.kept.scr], y1,
        by simp only [y2, hc.ctx.kept.scr], by rw [y3, BitVec.toNat_ofNat]; omega,
        by simp only [y4, hc.ctx.kept.scr]⟩).seq ?_
  refine (upd_pw (v := v) hS hG (fun hL _ _ _ _ _ _ hc => Covers.right (scCov hL hc.ctx (by unfold sMsg scrBytes; omega)))
    (fun hL a l hal => scD hL (.inr (by unfold sMsg; omega)) (by unfold sMsg scrBytes; omega)
      (by unfold scrBytes; omega))
    (fun hL hP => stkD hL (by omega) (by unfold sMsg scrBytes; omega))).seq ?_
  -- HMAC's `finalize` to the block.
  refine (pw_blk (X' := fun t => Ctr e.L i nbv t ∧
      XHF (dst + 32 * i) (BitVec.ofNat 64 (64 + (label.length + 4))) e.L t) [] tf nil
    fun g vv m₀ R EM t _ _ hc hx => WP.mono (prfFinArgs_ok hc.ctx.sp hc.slots (n := label.length + 4)
      (dst := dst) (by omega) hdst) fun u ⟨hs, z0, z1, z2, z3, z4⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, hG t u hx fun _ _ _ => by rw [hs.mem], by simp only [z0, hc.ctx.kept.scr],
        by simp only [z1, hc.ctx.kept.scr], z2, by simp only [z3, hx.1, hc.ctx.kept.scr]; exact shl5 i dst _,
        by simp only [z4, hc.ctx.kept.scr]⟩).seq ?_
  refine (hfin_pw (v := v) hS hG (o := dst + 32 * i) (by omega) (by omega)).seq ?_
  -- The counter.
  refine pw_blk [] tc nil fun g vv m₀ R EM t hL _ hc hx => WP.mono (hcount _ _ _ _ _ t hc hx.2)
    fun w ⟨Sw, mw, xw⟩ => ?_
  have hnQ := hL.nQ
  have Fw : Frame [⟨e.L.Q + BitVec.ofNat 64 oI, 8⟩] t.mem w.mem := by
    rw [mw]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have one : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  refine ⟨⟨R, EM, hc.step hL Sw.rd Sw.wr Sw.sp (fun r _ => by rw [Sw.v]) (fun r hr _ => Sw.cs r hr) Fw
    fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨oI, Nat.le_refl _, by show oI + 8 ≤ frameBytes; decide, rfl⟩)⟩,
    ⟨?_, ?_⟩, by rw [xw, hx.1, one]⟩
  · show w.mem.readW _ 64 = _
    rw [mw, Mem.readW_writeW_self64, hx.1, one]
  · show w.mem.readW _ 64 = _
    rw [mw, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact hx.2

theorem prfLoop_tr {S : Nat} (hS : 15 ≤ S) (e : Env) {label : List Nat} {len count : List Instr} {dst N : Nat}
    {nbv C : BitVec 64} (hN0 : 0 < N) (hN : N ≤ 256) (hd1 : 1040 ≤ dst) (hd2 : dst + 32 * N ≤ scrBytes)
    (hdst : dst < 4096) (hn : label.length + 4 ≤ 16) {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.AArch64.Taint.T}
    (tm : (taint.check (Taint.ofRegs [.x9]) (.block (msgBytes label len)) h₁).isSome = true)
    (tu : (taint.check (Taint.ofRegs []) (.block (prfUpdArgs (label.length + 4))) h₂).isSome = true)
    (tf : (taint.check (Taint.ofRegs []) (.block (prfFinArgs (label.length + 4) dst)) h₃).isSome = true)
    (tc : (taint.check (Taint.ofRegs []) (.block (incr count)) h₄).isSome = true)
    (hC : ∀ i < N, C - BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (N - (i + 1)))
    (hmsg : ∀ i < N, e.L.Ok → ∀ g vv m₀ R EM (u : State), Post e.L g vv m₀ R EM u → XH e.L i u →
      WP isa (.block (msgBytes label len)) u fun w => SameR u w ∧ Frame [⟨scA e.L sMsg, 16⟩] u.mem w.mem)
    (hcount : ∀ g vv m₀ R EM (u : State), Post e.L g vv m₀ R EM u → slot u e.L.Q oNB = nbv →
      WP isa (.block (incr count)) u fun w => SameR u w ∧
        w.mem = u.mem.writeW (e.L.Q + BitVec.ofNat 64 oI) (slot u e.L.Q oI + 1) ∧
        w.gpr .x12 = C - (slot u e.L.Q oI + 1)) :
    RelCT isa (PW S e (Ctr e.L 0 nbv)) (.loop (prfBody (HH v) label len dst count) (.nonzero .x .x12))
      fun _ _ => True :=
  (count_ct hN0 (fun i => PW S e (Ctr e.L i nbv)) fun i hi =>
    (prfBody_tr (v := v) hS e (i := i) (C := C) (by omega) (by omega) (by omega) hdst hn tm tu tf tc (hmsg i hi)
      hcount).mono (fun _ _ h => h) fun _ _ ⟨hL, hP, pa, pb, ⟨ca, xa⟩, ⟨cb, xb⟩⟩ =>
      ⟨⟨hL, hP, pa, pb, ca, cb⟩, by rw [xa, hC i hi]; exact Bytes.counter_ne hi (by omega),
        by rw [xb, hC i hi]; exact Bytes.counter_ne hi (by omega)⟩).mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The loops -/

theorem clLoop_tr {S : Nat} (hS : 15 ≤ S) (e : Env) :
    RelCT isa (PW S e fun _ => True) (clLoop (HH v)) fun _ _ => True :=
  (pw_blk (X' := Ctr e.L 0 (BitVec.ofNat 64 ((e.L.k.toNat + 31) / 32))) [] (by taint_decide)
    (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ _ R EM t hL _ hc _ =>
      WP.mono (clStart_ok hL hc) fun _ ⟨hc₁, ct₁, nb₁, _⟩ => ⟨⟨R, EM, hc₁⟩, ct₁, nb₁⟩).seq
  (prfLoop_tr (v := v) hS e (N := 8) (C := BitVec.ofNat 64 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (fun i hi => Offset.ofNat_sub_ofNat (by omega))
    (fun i hi hL _ _ _ _ _ u hu ⟨x9, x11, _⟩ => WP.mono (msgCL_ok x9 x11 (by omega) (hu.msgW hL))
      fun _ ⟨a, b, c, d, e, f, _⟩ => ⟨⟨a, b, c, d, e⟩, f⟩)
    fun _ _ _ _ _ u hu _ => WP.mono (incrCL_ok hu.ctx.sp hu.slots (hu.ctx.inFr (d := 184) (by decide)))
      fun _ hw => hw)

theorem amLoop_tr {S : Nat} (hS : 15 ≤ S) (e : Env) :
    RelCT isa (PW S e fun t => slot t e.L.Q oNB = BitVec.ofNat 64 ((e.L.k.toNat + 31) / 32)) (amLoop (HH v))
      fun _ _ => True := by
  refine (pw_blk (X' := Ctr e.L 0 (BitVec.ofNat 64 ((e.L.k.toNat + 31) / 32))) [] (by taint_decide)
    (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ _ R EM t hL _ hc hnb =>
      WP.mono (amStart_ok hL hc hnb) fun _ ⟨hc₁, ct₁, nb₁, _⟩ => ⟨⟨R, EM, hc₁⟩, ct₁, nb₁⟩).seq ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hk := hp.1.k1024
  exact (prfLoop_tr (v := v) hS e (N := (e.L.k.toNat + 31) / 32)
    (C := BitVec.ofNat 64 ((e.L.k.toNat + 31) / 32)) (by have := hp.1.k64; omega) (by omega) (by decide)
    (by unfold sAM scrBytes; omega) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (fun i hi => Offset.ofNat_sub_ofNat (by omega))
    (fun i hi hL _ _ _ _ _ u hu ⟨x9, x11, x12⟩ => WP.mono (msgAM_ok x9 x11 x12 (by omega) hk (hu.msgW hL))
      fun _ ⟨a, b, c, d, e, f, _⟩ => ⟨⟨a, b, c, d, e⟩, f⟩)
    fun _ _ _ _ _ u hu hnb => WP.mono (incrAM_ok hu.ctx.sp hu.slots (hu.ctx.inFr (d := 184) (by decide)))
      fun _ ⟨a, b, c⟩ => ⟨a, b, by rw [c, hnb]⟩) _ _ _ _ _ _ hp e₁ e₂

theorem clLoop_ct {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S fun L g vv m₀ t => ∃ R EM, KD L g vv m₀ R EM t) (clLoop (HH v))
      (Two S fun L g vv m₀ t => ∃ R EM kd, CLR L g vv m₀ R EM kd t) :=
  two_wp (fun e => (clLoop_tr hS e).mono (fun _ _ ⟨hL, hP, _, ⟨_, _, f₁⟩, ⟨_, _, f₂⟩⟩ =>
      ⟨hL, hP, ⟨_, _, f₁.post⟩, ⟨_, _, f₂.post⟩, trivial, trivial⟩) fun _ _ h => h)
    fun _ _ _ _ _ hL hP ⟨_, _, h⟩ => WP.mono (clLoop_ok hL (by omega) h.post h.kdk) fun _ h' => ⟨_, _, _, h'⟩

theorem amLoop_ct {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S fun L g vv m₀ t => ∃ R EM kd, CLR L g vv m₀ R EM kd t) (amLoop (HH v))
      (Two S fun L g vv m₀ t => ∃ R EM kd, AMR L g vv m₀ R EM kd t) :=
  two_wp (fun e => (amLoop_tr hS e).mono (fun _ _ ⟨hL, hP, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
      ⟨hL, hP, ⟨_, _, f₁.post⟩, ⟨_, _, f₂.post⟩, f₁.nb, f₂.nb⟩) fun _ _ h => h)
    fun _ _ _ _ _ hL hP ⟨_, _, _, h⟩ => WP.mono (amLoop_ok hL (by omega) h) fun _ h' => ⟨_, _, _, h'⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
