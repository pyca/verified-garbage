import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Correct

/-!
# Ed448 verification on AArch64: the whole function

`vg_ed448_verify` meets `vLocal` and the ABI (`verify_ok`), for any
implementation `v` of the Keccak permutation, given the reference
computations' agreement with the specification (`RecoverOk`, `VerifyEqOk`):
a context of 256 bytes or more returns 0; otherwise the frame
(`Proof.Ed25519.AArch64.Whole.wrap_ok`) runs the body, whose result is
RFC 8032's verification of the inputs as on entry.
-/

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Proof.Ed25519.AArch64.Whole (Saved entered bodyRd bodyWr)
open VG.Proof.Ed448.AArch64.Whole (sha3_bytesAt_length)

theorem wp_ite_t {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some true) (h : WP isa th s Q) : WP isa (.ite c th el) s Q := by
  obtain ⟨t, s', e, hq⟩ := h
  exact ⟨_, _, Exec.iteT hc e, hq⟩

theorem wp_ite_f {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some false) (h : WP isa el s Q) : WP isa (.ite c th el) s Q := by
  obtain ⟨t, s', e, hq⟩ := h
  exact ⟨_, _, Exec.iteF hc e, hq⟩

/-- What `lsr x9, x2, #8` does. -/
abbrev LsrPost (s t : State) : Prop :=
  t.gpr .x9 = s.gpr .x2 >>> 8 ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
    t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v

theorem lsr_ok (s : State) : WP isa (.block [.lsr .x .x9 .x2 8]) s (LsrPost s) := by
  apply WP.of_runBlock
  simp only [LsrPost, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, Nat.reduceLT,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, rfl, rfl⟩

theorem lsr_pre {s t : State} (h : vLocal.pre s) (ht : LsrPost s t) : vLocal.pre t := by
  obtain ⟨_, e, _, trd, twr, tsp, _⟩ := ht
  simp only [vLocal, e _ (by decide : Reg.x0 ≠ .x9), e _ (by decide : Reg.x1 ≠ .x9),
    e _ (by decide : Reg.x2 ≠ .x9), e _ (by decide : Reg.x3 ≠ .x9), e _ (by decide : Reg.x4 ≠ .x9),
    e _ (by decide : Reg.x5 ≠ .x9), e _ (by decide : Reg.x6 ≠ .x9), trd, twr, tsp]
  exact h

theorem lsr_pub {s₁ s₂ t₁ t₂ : State} (h : vLocal.pub s₁ s₂) (h₁ : LsrPost s₁ t₁) (h₂ : LsrPost s₂ t₂) :
    vLocal.pub t₁ t₂ := by
  obtain ⟨_, e₁, _, _, _, sp₁, _⟩ := h₁
  obtain ⟨_, e₂, _, _, _, sp₂, _⟩ := h₂
  simp only [vLocal, e₁ _ (by decide : Reg.x0 ≠ .x9), e₁ _ (by decide : Reg.x1 ≠ .x9),
    e₁ _ (by decide : Reg.x2 ≠ .x9), e₁ _ (by decide : Reg.x3 ≠ .x9), e₁ _ (by decide : Reg.x4 ≠ .x9),
    e₁ _ (by decide : Reg.x5 ≠ .x9), e₁ _ (by decide : Reg.x6 ≠ .x9),
    e₂ _ (by decide : Reg.x0 ≠ .x9), e₂ _ (by decide : Reg.x1 ≠ .x9),
    e₂ _ (by decide : Reg.x2 ≠ .x9), e₂ _ (by decide : Reg.x3 ≠ .x9), e₂ _ (by decide : Reg.x4 ≠ .x9),
    e₂ _ (by decide : Reg.x5 ≠ .x9), e₂ _ (by decide : Reg.x6 ≠ .x9), sp₁, sp₂]
  exact h

theorem lsr_zero {s t : State} (ht : LsrPost s t) : t.gpr .x9 = 0 ↔ (s.gpr .x2).toNat < 256 := by
  rw [ht.1]
  constructor
  · intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
    change _ = 0 at this
    omega
  · intro hc
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; show _ = 0; omega

theorem lsr_x2 {s t : State} (ht : LsrPost s t) : t.gpr .x2 = s.gpr .x2 := ht.2.1 _ (by decide)

theorem movz0_ok (s : State) :
    WP isa (.block [.movz .x .x0 0 0]) s fun t => t.gpr .x0 = 0 ∧
      (∀ r, r ≠ .x0 → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.v = s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl⟩

theorem body_depth (v : Proof.Sha3.AArch64.Permutation) : (body v.callee).aarch64Depth ≤ 1 := by
  have ha := v.absorb_depth
  have hp := v.pad_depth
  have hs := v.squeeze_depth
  have hr := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames VG.Proof.Ed448.AArch64.Whole.reduce_noFrames
  have he := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames VG.Proof.Ed448.AArch64.Whole.equation_noFrames
  simp only [body, Impl.Ed448.AArch64.Verify.hash, Impl.Ed448.AArch64.Whole.zeroSt,
    Impl.Ed448.AArch64.Whole.kabs, Impl.Ed448.AArch64.Whole.kpad, Impl.Ed448.AArch64.Whole.ksqz,
    Impl.Ed448.AArch64.Whole.callS, Code.aarch64Depth, Nat.max_le, ha, hp, hs, hr, he]
  omega

/-- The hash of the specification, as the body computes it. -/
theorem verify_eq (pk ctx msg sig : List Byte) (hc : ctx.length < 256) :
    Spec.Ed448.verify pk ctx msg sig = Spec.Ed448.verifyEquation pk sig (Spec.Ed448.scalarReduce
      (Spec.Sha3.shake256 ("SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++
        [BitVec.ofNat 8 0, BitVec.ofNat 8 ctx.length] ++ ctx ++ sig.take 57 ++ pk ++ msg) 114)) := by
  simp only [Spec.Ed448.verify, Spec.Ed448.hash, Spec.Ed448.dom4, List.append_assoc,
    show ctx.length ≤ 255 from by omega, decide_true, Bool.true_and]

/-- An input's bytes after the frame's writes, as on entry. -/
theorem frame_bytes {m m' : Mem} {S R : Region} (hf : Frame [S] m m') (hd : S.Disjoint R) {n : Nat}
    (hn : n ≤ R.len) (hl : R.len ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt m' R.base n = Spec.Sha3.bytesAt m R.base n := by
  unfold Spec.Sha3.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := R) ?_ hl (by have := List.mem_range.mp hi; omega)
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact hd.symm

theorem ed448_bytesAt (m : Mem) (p : Addr) (n : Nat) :
    Spec.Ed448.bytesAt m p n = Spec.Sha3.bytesAt m p n := rfl

theorem take57' (m : Mem) (p : Addr) :
    (Spec.Sha3.bytesAt m p 114).take 57 = Spec.Sha3.bytesAt m p 57 := by
  simp [Spec.Sha3.bytesAt, ← List.map_take, List.take_range]

theorem entry_ctx {s p : State} (h : vLocal.pre s) (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    Ctx0 (lay s) s.gpr s.v p.mem (p.withRegions (bodyRd s) (bodyWr s)) := by
  have hc := VG.Proof.Ed25519.AArch64.Whole.saved_ctx hp
  simpa only [bodyRd, bodyWr, h.1, h.2.1, Ctx0, Lay.env, Lay.inputs, Lay.PK, Lay.CTX, Lay.MSG,
    Lay.SIG, Lay.SCR, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) : Args (lay s) p.mem := fun j hj => by
  have hw := VG.Proof.Ed25519.AArch64.Whole.saved_words hp hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw

theorem entry_x6 {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    (p.withRegions (bodyRd s) (bodyWr s)).gpr .x6 = (lay s).scr :=
  hp.step.regs .x6 (by decide)

theorem body_ctx {s p u : State} (h : vLocal.pre s) (hu : Ctx0 (lay s) s.gpr s.v p.mem u) :
    VG.Proof.Ed25519.AArch64.Whole.Ctx (VG.Proof.Ed25519.AArch64.Whole.base s) s.gpr s.v p.mem (bodyRd s)
      s.wr u := by
  simpa only [bodyRd, bodyWr, h.1, h.2.1, Ctx0, Lay.env, Lay.inputs, Lay.PK, Lay.CTX, Lay.MSG,
    Lay.SIG, Lay.SCR, lay, List.cons_append, List.nil_append] using hu

theorem verify_ok (v : Proof.Sha3.AArch64.Permutation) (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk)
    {s : State} (h : vLocal.pre s) :
    WP isa (verifyWith v.callee) s fun u => abiPreserved s u ∧ vLocal.post s u := by
  refine WP.seq (WP.mono (lsr_ok s) fun t ht => ?_)
  have ⟨_, tg, tm, _, _, tsp, tv⟩ := ht
  have e : ∀ r, r ≠ .x9 → t.gpr r = s.gpr r := tg
  have hpre : vLocal.pre t := lsr_pre h ht
  have hpost : ∀ u, vLocal.post t u → vLocal.post s u := fun u hu => by
    simp only [vLocal, e _ (by decide : Reg.x0 ≠ .x9), e _ (by decide : Reg.x1 ≠ .x9),
      e _ (by decide : Reg.x2 ≠ .x9), e _ (by decide : Reg.x3 ≠ .x9), e _ (by decide : Reg.x4 ≠ .x9),
      e _ (by decide : Reg.x5 ≠ .x9), tm] at hu
    exact hu
  have habi : ∀ u, abiPreserved t u → abiPreserved s u := fun u ⟨hg, hsp, hv⟩ =>
    ⟨fun r hr => (hg r hr).trans (tg r (by rintro rfl; simp [preserved] at hr)), hsp.trans tsp,
      fun r hr => by rw [hv r hr, tv]⟩
  have hc2 : (t.gpr .x2).toNat = (s.gpr .x2).toNat := by rw [e _ (by decide)]
  by_cases hc : (s.gpr .x2).toNat < 256
  · -- The frame and the body.
    have h9 : t.gpr .x9 = 0 := (lsr_zero ht).2 hc
    refine wp_ite_t (by simp [eval, State.read, h9]) ?_
    have hc' : (t.gpr .x2).toNat < 256 := hc2 ▸ hc
    have hL := lay_ok hpre hc'
    refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.wrap_ok (body_depth v) hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (fun r hr => by
        rw [hpre.2.1] at hr; simp only [List.mem_singleton] at hr; subst hr; exact hpre.2.2.2.2.2.2.2.2.2.2.1)
      (P := fun m _ x0 => x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt m (t.gpr .x0) 57)
        (Spec.Ed448.bytesAt m (t.gpr .x5) 114) (Spec.Ed448.scalarReduce
          (Spec.Sha3.shake256 (hashIn (lay t) m) 114)) then 1 else 0) fun p hp => ?_)
      fun u ⟨hu, m, hf, hx⟩ => ⟨habi u hu, hpost u ?_⟩
    · refine WP.mono (body_ok v hR hE hL (entry_ctx hpre hp) (entry_args hp) (entry_x6 hp))
        fun u ⟨hu, hx⟩ => ⟨body_ctx hpre hu, hx⟩
    · have hb : ∀ R ∈ (lay t).inputs, ∀ n ≤ R.len, R.len ≤ 2 ^ 64 →
          Spec.Sha3.bytesAt m R.base n = Spec.Sha3.bytesAt t.mem R.base n := by
        intro R hR n hn hl
        refine frame_bytes hf ?_ hn hl
        simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl | rfl | rfl
        exacts [hL.kp, hL.kx, hL.km, hL.ks]
      have hpk := hb (lay t).PK (by simp [Lay.inputs]) 57 (Nat.le_refl _) (by change 57 ≤ 2 ^ 64; decide)
      have hcx := hb (lay t).CTX (by simp [Lay.inputs]) (t.gpr .x2).toNat (Nat.le_refl _) (Nat.le_of_lt (BitVec.isLt _))
      have hms := hb (lay t).MSG (by simp [Lay.inputs]) (t.gpr .x4).toNat (Nat.le_refl _) (Nat.le_of_lt (BitVec.isLt _))
      have hsg := hb (lay t).SIG (by simp [Lay.inputs]) 114 (Nat.le_refl _) (by change 114 ≤ 2 ^ 64; decide)
      have hs57 := hb (lay t).SIG (by simp [Lay.inputs]) 57 (by change 57 ≤ 114; decide) (by change 114 ≤ 2 ^ 64; decide)
      simp only [lay] at hpk hcx hms hsg hs57
      show u.gpr .x0 = _
      rw [hx, verify_eq _ _ _ _ (by rw [ed448_bytesAt, sha3_bytesAt_length]; exact hc')]
      simp only [ed448_bytesAt, take57', sha3_bytesAt_length, hashIn, hdrBytes, lay, List.append_assoc,
        hpk, hcx, hms, hsg, hs57]
  · -- A context of 256 bytes or more.
    have h9 : t.gpr .x9 ≠ 0 := fun h0 => hc ((lsr_zero ht).1 h0)
    refine wp_ite_f (by simp only [eval, State.read, Option.some.injEq, beq_eq_false_iff_ne]; exact h9) ?_
    refine WP.mono (movz0_ok t) fun u ⟨u0, ug, usp, uv⟩ => ⟨habi u ⟨fun r hr => ug r (by
      rintro rfl; simp [preserved] at hr), usp, fun r _ => by rw [uv]⟩, hpost u ?_⟩
    show u.gpr .x0 = _
    rw [u0, Spec.Ed448.verify, ed448_bytesAt, sha3_bytesAt_length]
    simp only [show ¬ (t.gpr .x2).toNat ≤ 255 by omega, decide_false, Bool.false_and]
    rfl

end VG.Proof.Ed448.AArch64.Verify
