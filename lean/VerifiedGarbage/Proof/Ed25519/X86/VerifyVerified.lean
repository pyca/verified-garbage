import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.X86.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.WindowStep`. -/
section

/-!
# Verification's windows

A window doubles the sum four times (`dbl-2008-hwcd`, `dblPoint_rep`), reads a
digit of a scalar from the inputs (a nibble of the byte `esi`), and adds the
digit's entry of a table, unless the digit is zero. The sum represents a
multiple of `A` plus a multiple of `-B` throughout (`Rep`).
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards
open VG.Impl.X25519.X86 (sc at_)

/-! ## Doublings -/

theorem dblOps_eval (e : Env) : point (evalOps dblOps e) 0 1 2 3 = dblPoint (point e 0 1 2 3) := rfl

theorem dbl_ok {s : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s) {a : EPoint dZ}
    (h : Rep (point (env s.mem x) 0 1 2 3) a) :
    WP isa dbl s fun t => FieldKeep x s t ∧ Rep (point (env t.mem x) 0 1 2 3) (a + a) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.mono (fieldCode_ok dblOps hc) fun t ⟨kt, vt⟩ => ⟨kt, ?_, fun i hi => ?_⟩
  · rw [vt, dblOps_eval]; exact dblPoint_rep h.proj
  · rw [vt]; exact point_ops_high _ (by decide) _ i hi

theorem two_smul_add (a : EPoint dZ) (n : Nat) : n • a + n • a = (2 * n) • a := by
  rw [← two_nsmul, smul_smul]

theorem doubleWindow_ok {s : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s) {a : EPoint dZ}
    (h : Rep (point (env s.mem x) 0 1 2 3) a) :
    WP isa doubleWindow s fun t => IKeep x s t ∧ t.gpr .esi = s.gpr .esi ∧
      Rep (point (env t.mem x) 0 1 2 3) ((16 : Nat) • a) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  rw [← one_nsmul a] at h
  refine WP.seq (WP.mono (dbl_ok hc h) fun b ⟨kb, rb, hb⟩ => ?_)
  rw [two_smul_add] at rb
  refine WP.seq (WP.mono (dbl_ok (kb.ctx hc) rb) fun c ⟨kc, rc, hc'⟩ => ?_)
  rw [two_smul_add] at rc
  refine WP.seq (WP.mono (dbl_ok ((kb.trans kc).ctx hc) rc) fun d ⟨kd, rd, hd⟩ => ?_)
  rw [two_smul_add] at rd
  refine WP.mono (dbl_ok ((kb.trans kc |>.trans kd).ctx hc) rd) fun t ⟨kt, rt, ht⟩ =>
    ⟨IKeep.of_field (((kb.trans kc).trans kd).trans kt), (((kb.trans kc).trans kd).trans kt).keep.esi,
      ?_, fun i hi => ?_⟩
  · rw [two_smul_add] at rt; exact rt
  · rw [ht i hi, hd i hi, hc' i hi, hb i hi]

/-! ## Digits -/

/-- What reading a digit leaves: everything but `eax` and the flags. -/
structure EaxKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .eax → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem EaxKeep.trans {s t u : State} (h : EaxKeep s t) (k : EaxKeep t u) : EaxKeep s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.mem.trans h.mem, k.rd.trans h.rd, k.wr.trans h.wr⟩

theorem EaxKeep.of_upd {s t : State} {v : BitVec 32} (h : Wp.Upd s t .eax v) : EaxKeep s t :=
  ⟨h.other, h.mem, h.rd, h.wr⟩

theorem EaxKeep.ikeep {x : BitVec 32} {s t : State} (h : EaxKeep s t) : IKeep x s t :=
  ⟨h.gpr _ (by decide), h.gpr _ (by decide), h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩

theorem bytesAt_getD (m : Mem) (p : Addr) (n i : Nat) (hi : i < n) :
    (Spec.Ed25519.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, hi]

theorem digitByte_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s)
    {a add n i : Nat} (ha : a < 4) (hsl : SlicePre s₀ 3 (arg s₀ a + BitVec.ofNat 32 add) n) (hi : i < n)
    (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (.block (digitByte (4 + 4 * a) add)) s fun t => EaxKeep s t ∧
      t.gpr .eax = ((Spec.Ed25519.bytesAt s₀.mem ((arg s₀ a + BitVec.ofNat 32 add).setWidth 64) n).getD i
        0).setWidth 32 := by
  refine Wp.wp_ldm hs.esp (by rw [hs.rd, hs.wr]; exact hp.argIn ha) fun u hu => ?_
  have eu : u.gpr .eax = arg s₀ a := by rw [hu.gpr]; exact hp.arg_same hs.frame ha
  refine Wp.wp_add fun v hv _ => ?_
  have ev : v.gpr .eax = arg s₀ a + BitVec.ofNat 32 i := by
    rw [hv.gpr, eu, hu.other .esi (by decide), hesi]
  have hA : addr (v.gpr .eax) add = addr (arg s₀ a + BitVec.ofNat 32 add) i := by
    rw [ev]; simp only [addr]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 i)]
  have hrd : v.rd ++ v.wr = s₀.rd ++ s₀.wr := by rw [hv.rd, hv.wr, hu.rd, hu.wr, hs.rd, hs.wr]
  refine scalar_ld8 hA (by rw [hrd]; exact slice_read hsl (by omega) (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨(EaxKeep.of_upd hu).trans ((EaxKeep.of_upd hv).trans (EaxKeep.of_upd ht)), ?_⟩
  rw [ht.gpr, hv.mem, hu.mem, bytesAt_getD _ _ _ _ hi,
    ← addr_eq (by have := hsl.fit; omega)]
  congr 1
  apply hs.frame
  intro r hr; rw [List.mem_singleton.mp hr]
  exact hsl.sep _ (slice_contains hsl (by omega) (by decide))

private theorem nibble_fact : ∀ b : BitVec 8,
    b.setWidth 32 >>> 4 = BitVec.ofNat 32 (b.toNat / 16) ∧
    b.setWidth 32 &&& 15 = BitVec.ofNat 32 (b.toNat % 16) := by decide

theorem digitHigh_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s)
    {a add n i : Nat} (ha : a < 4) (hsl : SlicePre s₀ 3 (arg s₀ a + BitVec.ofNat 32 add) n) (hi : i < n)
    (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (.block (digitHigh (4 + 4 * a) add)) s fun t => EaxKeep s t ∧
      t.gpr .eax = BitVec.ofNat 32 (((Spec.Ed25519.bytesAt s₀.mem
        ((arg s₀ a + BitVec.ofNat 32 add).setWidth 64) n).getD i 0).toNat / 16) := by
  refine WP.block_append (WP.mono (digitByte_ok hp hs ha hsl hi hesi) fun u ⟨ku, eu⟩ => ?_)
  refine Wp.wp_shr (by decide) fun t ht _ => WP.block_nil ⟨ku.trans ?_, ?_⟩
  · exact ⟨fun r hr => ht.other r hr, ht.mem, ht.rd, ht.wr⟩
  · rw [ht.gpr, eu]; exact (nibble_fact _).1

theorem digitLow_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s)
    {a add n i : Nat} (ha : a < 4) (hsl : SlicePre s₀ 3 (arg s₀ a + BitVec.ofNat 32 add) n) (hi : i < n)
    (hesi : s.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (.block (digitLow (4 + 4 * a) add)) s fun t => EaxKeep s t ∧
      t.gpr .eax = BitVec.ofNat 32 (((Spec.Ed25519.bytesAt s₀.mem
        ((arg s₀ a + BitVec.ofNat 32 add).setWidth 64) n).getD i 0).toNat % 16) := by
  refine WP.block_append (WP.mono (digitByte_ok hp hs ha hsl hi hesi) fun u ⟨ku, eu⟩ => ?_)
  refine Wp.wp_andi fun t ht => WP.block_nil ⟨ku.trans (EaxKeep.of_upd ht), ?_⟩
  rw [ht.gpr, eu]; exact (nibble_fact _).2

/-! ## Adding a digit's entry -/

theorem entryAddr_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (o : Nat) {v : Nat} (hv : 1 ≤ v)
    (hv' : v < 16) (he : s.gpr .eax = BitVec.ofNat 32 v) :
    WP isa (.block (entryAddr o)) s fun t =>
      VG.Proof.X25519.X86.Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 (o + 128 * (v - 1)) := by
  refine Wp.wp_subi fun s₁ h₁ _ _ => Wp.wp_movi fun s₂ h₂ => VG.Proof.X25519.X86.wp_mul fun s₃ h₃ => ?_
  refine Wp.wp_add fun s₄ h₄ _ => Wp.wp_addi fun s₅ h₅ => Wp.wp_mov fun s₆ h₆ => WP.block_nil ?_
  have hk : VG.Proof.X25519.X86.Keep s s₆ := (VG.Proof.X25519.X86.updKeep h₁).trans ((VG.Proof.X25519.X86.updKeep h₂).trans (h₃.keep.trans
    ((VG.Proof.X25519.X86.updKeep h₄).trans ((VG.Proof.X25519.X86.updKeep h₅).trans (VG.Proof.X25519.X86.updKeep h₆)))))
  have e₁ : s₁.gpr .eax = BitVec.ofNat 32 (v - 1) := by rw [h₁.gpr, he]; exact Wp.ofNat_pred hv
  have hvv : s₃.gpr .eax = BitVec.ofNat 32 (128 * (v - 1)) := by
    apply BitVec.eq_of_toNat_eq
    change VG.Proof.X25519.X86.v s₃ .eax = _
    rw [h₃.eax]
    simp only [VG.Proof.X25519.X86.v, h₂.other .eax (by decide), e₁, h₂.gpr, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show v - 1 < 2 ^ 32 by omega)]
    exact congrArg (fun n => n % 2 ^ 32) (Nat.mul_comm (v - 1) 128)
  refine ⟨hk, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  rw [h₆.gpr, h₅.gpr, h₄.gpr, hvv, h₃.other .edi (by decide) (by decide),
    h₂.other .edi (by decide), h₁.other .edi (by decide), hc.edi]
  rw [BitVec.add_comm (BitVec.ofNat 32 (128 * (v - 1))) x, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.add_comm (128 * (v - 1)) o]

theorem digit_test_fact : ∀ v < 16, (BitVec.ofNat 32 v &&& BitVec.ofNat 32 v == 0) = decide (v = 0) := by
  decide

theorem addDigit_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {o : Nat} (ho : 1024 ≤ o)
    (hn : o + 1920 ≤ 8192) {v : Nat} (hv : v < 16) (he : s.gpr .eax = BitVec.ofNat 32 v)
    {X a : EPoint dZ} (htab : ∀ j < 15, Rep (tablePoint s.mem x (o + 128 * j)) ((j + 1) • X))
    (hacc : Rep (point (env s.mem x) 0 1 2 3) a) (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (addDigit o) s fun t => IKeep x s t ∧ t.gpr .esi = s.gpr .esi ∧
      Rep (point (env t.mem x) 0 1 2 3) (a + v • X) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  have htest : WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t =>
      IKeep x s t ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.zf = some (decide (v = 0)) :=
    Wp.wp_test fun t ht zt => WP.block_nil ⟨⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
      by rw [ht.mem]; exact Frame.refl _ _⟩, ht.mem, ht.gpr, by rw [zt, he, digit_test_fact v hv]⟩
  refine WP.seq (WP.mono htest fun u ⟨ku, mu, gu, zu⟩ => ?_)
  have cu := ku.ctx hc
  refine WP.ite (!decide (v = 0)) (by show u.zf.map (!·) = _; rw [zu]; rfl) (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := by simpa using h
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (entryAddr_ok cu o (by omega) hv (by rw [gu]; exact he)) fun b ⟨kb, mb, pb⟩ => ?_
    have cb := kb.ctx cu
    rw [WP.block_append_iff]
    refine WP.mono (pointFromTableQ_ok cb pb (by omega) (by omega)) fun c ⟨kc, ec, pc, hc'⟩ => ?_
    have cc := kc.ctx cb
    refine WP.mono (pointAdd_ok cc (by rw [hc' 16 (Or.inr (by decide)), mb, mu]; exact hd))
      fun t ⟨kt, pt, ht⟩ => ⟨((ku.trans (IKeep.of_mem kb mb)).trans kc).trans (IKeep.of_field kt), ?_, ?_,
        fun i hi => ?_⟩
    · rw [kt.keep.esi, ec, kb.esi, gu]
    · have p0 : point (env c.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
        simp only [point, hc' 0 (Or.inl (by decide)), hc' 1 (Or.inl (by decide)),
          hc' 2 (Or.inl (by decide)), hc' 3 (Or.inl (by decide)), mb, mu]
      rw [pt, p0, pc, mb, mu]
      have := htab (v - 1) (by omega)
      rw [show v - 1 + 1 = v by omega] at this
      exact pointAdd_rep hacc this
    · rw [ht i hi, hc' i (Or.inr (by omega)), mb, mu]
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    refine WP.block_nil ⟨ku, by rw [gu], ?_, fun i _ => by rw [mu]⟩
    rw [mu, zero_smul, add_zero]; exact hacc

/-! ## Windows -/

/-- What the windows keep: the saved state, `d`, both tables and `R`. -/
structure WinCtx (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (s : State) : Prop where
  pre : VerifyPre s₀
  saved : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s
  d : env s.mem (arg s₀ 3) 16 = Spec.Ed25519.d
  ta : ∀ j < 15, Rep (tablePoint s.mem (arg s₀ 3) (1024 + 128 * j)) ((j + 1) • Aa)
  tb : ∀ j < 15, Rep (tablePoint s.mem (arg s₀ 3) (3072 + 128 * j)) ((j + 1) • (-baseAff))
  r : tablePoint s.mem (arg s₀ 3) 7808 = R

theorem WinCtx.ctx {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) : VG.Proof.Ed25519.X86.Ctx (arg s₀ 3) s :=
  h.saved.ctx h.pre.scratch.fit h.pre.scratch.wr

theorem WinCtx.of_ikeep {s₀ s t : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) (k : IKeep (arg s₀ 3) s t)
    (hd : env t.mem (arg s₀ 3) 16 = env s.mem (arg s₀ 3) 16) : WinCtx s₀ Aa R t := by
  have hfit := h.pre.scratch.fit
  refine ⟨h.pre, h.saved.ikeep hfit k, hd.trans h.d, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · rw [tablePoint_frame hfit k.frame (by decide) (by omega) (Or.inr (by omega))]; exact h.ta j hj
  · rw [tablePoint_frame hfit k.frame (by decide) (by omega) (Or.inr (by omega))]; exact h.tb j hj
  · rw [tablePoint_frame hfit k.frame (by decide) (by decide) (Or.inr (by decide))]; exact h.r

theorem windowWith_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {o : Nat} (ho : 1024 ≤ o) (hn : o + 1920 ≤ 8192) {X : EPoint dZ}
    (htab : ∀ t, WinCtx s₀ Aa R t → ∀ j < 15, Rep (tablePoint t.mem (arg s₀ 3) (o + 128 * j)) ((j + 1) • X))
    {digit : List Instr} {v : Nat} (hv : v < 16)
    (hdig : ∀ t, WinCtx s₀ Aa R t → t.gpr .esi = s.gpr .esi →
      WP isa (.block digit) t fun u => EaxKeep t u ∧ u.gpr .eax = BitVec.ofNat 32 v)
    {a : EPoint dZ} (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) a) :
    WP isa (windowWith o digit) s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = s.gpr .esi ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) ((16 : Nat) • a + v • X) := by
  refine WP.seq (WP.mono (doubleWindow_ok h.ctx hacc) fun b ⟨kb, eb, rb, hb⟩ => ?_)
  have wb := h.of_ikeep kb (hb 16 (by decide))
  refine WP.seq (WP.mono (hdig b wb eb) fun c ⟨kc, ec⟩ => ?_)
  have wc := wb.of_ikeep kc.ikeep (by rw [kc.mem])
  have rc : Rep (point (env c.mem (arg s₀ 3)) 0 1 2 3) ((16 : Nat) • a) := by rw [kc.mem]; exact rb
  refine WP.mono (addDigit_ok wc.ctx ho hn hv ec (htab c wc) rc wc.d) fun t ⟨kt, et, rt, ht⟩ =>
    ⟨wc.of_ikeep kt (ht 16 (by decide)), ?_, rt⟩
  rw [et, kc.gpr _ (by decide)]; exact eb

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyDecode`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verify_sig_offset {s : State} (h : verifyLocal.pre s) :
    (arg s 1 + BitVec.ofNat 32 32).setWidth 64 = (arg s 1).setWidth 64 + BitVec.ofNat 64 32 := by
  obtain ⟨_, _, _, _, _, _, _, _, sf, _, _, _⟩ := h
  exact addr_eq (by omega_using [sf])

theorem VerifyCTFacts.pkBytes {s t : State} (h : VerifyCTFacts s t) :
    VG.Spec.Ed25519.bytesAt s.mem ((arg s 0 + BitVec.ofNat 32 0).setWidth 64) 32 =
      VG.Spec.Ed25519.bytesAt t.mem ((arg t 0 + BitVec.ofNat 32 0).setWidth 64) 32 := by
  simpa only [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] using h.pub.2.2.2.2.2.1

theorem VerifyCTFacts.rBytes {s t : State} (h : VerifyCTFacts s t) :
    VG.Spec.Ed25519.bytesAt s.mem ((arg s 1 + BitVec.ofNat 32 0).setWidth 64) 32 =
      VG.Spec.Ed25519.bytesAt t.mem ((arg t 1 + BitVec.ofNat 32 0).setWidth 64) 32 := by
  have hh := congrArg (List.take 32) h.pub.2.2.2.2.2.2.1
  rw [signatureBytes_take, signatureBytes_take] at hh
  simpa only [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] using hh

theorem VerifyCTFacts.scalarBytes {s t : State} (h : VerifyCTFacts s t) :
    VG.Spec.Ed25519.bytesAt s.mem ((arg s 1 + BitVec.ofNat 32 32).setWidth 64) 32 =
      VG.Spec.Ed25519.bytesAt t.mem ((arg t 1 + BitVec.ofNat 32 32).setWidth 64) 32 := by
  rw [VG.Proof.Ed25519.X86.verify_sig_offset h.left, VG.Proof.Ed25519.X86.verify_sig_offset h.right]
  have hh := congrArg (List.drop 32) h.pub.2.2.2.2.2.2.1
  rw [signatureBytes_drop, signatureBytes_drop] at hh
  exact hh

theorem VerifyCTFacts.challengeBytes {s t : State} (h : VerifyCTFacts s t) :
    VG.Spec.Ed25519.bytesAt s.mem ((arg s 2 + BitVec.ofNat 32 0).setWidth 64) 64 =
      VG.Spec.Ed25519.bytesAt t.mem ((arg t 2 + BitVec.ofNat 32 0).setWidth 64) 64 := by
  simpa only [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] using h.pub.2.2.2.2.2.2.2

theorem fe_decode_input {s : State} {p : BitVec 32} (h : p.toNat + 32 ≤ 2 ^ 32) :
    VG.Proof.X25519.X86.fe s.mem p 0 = VG.Spec.Ed25519.decodeLE (VG.Spec.Ed25519.bytesAt s.mem (p.setWidth 64) 32) := by
  have hh := decode_words (x := p) (o := 0) s.mem 8 (by omega_using [h])
  rw [VG.Proof.X25519.X86.addr_zero] at hh
  exact hh.symm

theorem VerifyCTFacts.scalarFe {s t : State} (h : VerifyCTFacts s t) :
    VG.Proof.X25519.X86.fe s.mem (arg s 1 + 32) 0 = VG.Proof.X25519.X86.fe t.mem (arg t 1 + 32) 0 := by
  change VG.Proof.X25519.X86.fe s.mem (arg s 1 + BitVec.ofNat 32 32) 0 = VG.Proof.X25519.X86.fe t.mem (arg t 1 + BitVec.ofNat 32 32) 0
  rw [VG.Proof.Ed25519.X86.fe_decode_input (s := s) (verify_pre h.left).scalar.fit, VG.Proof.Ed25519.X86.fe_decode_input (s := t) (verify_pre h.right).scalar.fit]
  exact congrArg VG.Spec.Ed25519.decodeLE h.scalarBytes

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyDecodeInput`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem decodeNumber_spec (bs : List Byte) (hl : bs.length = 32) :
    decodeNumber (Spec.Ed25519.decodeLE bs) = Spec.Ed25519.decodePoint bs := by
  rw [decodePoint32 bs hl]
  by_cases hy : Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P
  · rw [decodeNumber, dite_eq_left hy, ite_eq_left hy, toFe_of_lt _ hy]
    rfl
  · rw [decodeNumber, dite_eq_right hy, ite_eq_right hy]

def inputPoint (s : State) (i : Nat) : Option Spec.Ed25519.Point :=
  Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem ((arg s i + BitVec.ofNat 32 0).setWidth 64) 32)

theorem decodeInput_number_ok {s₀ s : State} {i : Nat} (hp : ScratchPre s₀ 3 4)
    (hi : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 0) 32)
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s) (hia : i < 4) :
    WP isa (.seq (.block (inputSliceWords i 0 96 8)) pointDecode) s fun t =>
      VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) t ∧ VG.Frame [VG.Proof.X25519.X86.sub (arg s₀ 3) 24 7144] s.mem t.mem ∧
      DecodeResult (arg s₀ 3) (decodeNumber (VG.Proof.X25519.X86.fe s₀.mem (arg s₀ i + BitVec.ofNat 32 0) 0)) t := by
  refine WP.seq (WP.mono (inputSliceWords_ok hp hi hs hia (by decide) (by decide) (by decide))
    fun a ⟨ha, wa, fa⟩ => ?_)
  refine WP.mono (pointDecode_ok (ha.ctx hp.fit hp.wr)) fun t ht => ?_
  have kt := ht.1
  refine ⟨ha.mulkeep hp.fit kt, (VG.Proof.X25519.X86.frameWiden fa hp.fit (by decide) (by decide) (by decide)).trans kt.frame, ?_⟩
  have value : VG.Proof.X25519.X86.fe a.mem (arg s₀ 3) 96 = VG.Proof.X25519.X86.fe s₀.mem (arg s₀ i + BitVec.ofNat 32 0) 0 := by
    apply VG.Proof.X25519.X86.num_congr
    intro k hk
    simp only [Nat.zero_add]
    exact congrArg BitVec.toNat (wa k hk)
  with_reducible exact Eq.mp (congrArg (fun n => DecodeResult (arg s₀ 3) (decodeNumber n) t) value) ht.2

theorem inputPoint_number {s : State} {i : Nat} (hi : SlicePre s 3 (arg s i + BitVec.ofNat 32 0) 32) :
    decodeNumber (VG.Proof.X25519.X86.fe s.mem (arg s i + BitVec.ofNat 32 0) 0) = VG.Proof.Ed25519.X86.inputPoint s i := by
  have hv : VG.Proof.X25519.X86.fe s.mem (arg s i + BitVec.ofNat 32 0) 0 = Spec.Ed25519.decodeLE
      (Spec.Ed25519.bytesAt s.mem ((arg s i + BitVec.ofNat 32 0).setWidth 64) 32) := by
    rw [← VG.Proof.X25519.X86.addr_zero (arg s i + BitVec.ofNat 32 0)]
    exact (decode_words s.mem 8 (by have := hi.fit; omega_using [this])).symm
  exact (congrArg decodeNumber hv).trans (VG.Proof.Ed25519.X86.decodeNumber_spec _
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]))

theorem decodeInput_ok {s₀ s : State} {i : Nat} (hp : ScratchPre s₀ 3 4)
    (hi : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 0) 32)
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s) (hia : i < 4) :
    WP isa (.seq (.block (inputSliceWords i 0 96 8)) pointDecode) s fun t =>
      VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) t ∧ VG.Frame [VG.Proof.X25519.X86.sub (arg s₀ 3) 24 7144] s.mem t.mem ∧
      DecodeResult (arg s₀ 3) (VG.Proof.Ed25519.X86.inputPoint s₀ i) t := by
  refine WP.mono (VG.Proof.Ed25519.X86.decodeInput_number_ok hp hi hs hia) fun t ht => ⟨ht.1, ht.2.1, ?_⟩
  with_reducible exact Eq.mp (congrArg (fun p => DecodeResult (arg s₀ 3) p t) (VG.Proof.Ed25519.X86.inputPoint_number hi)) ht.2.2

theorem decodedThen_ok {s₀ s : State} {p : Option Spec.Ed25519.Point} {next : Prog isa} {P : State → Prop}
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s) (hr : DecodeResult (arg s₀ 3) p s)
    (hn : ∀ t, VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) t → t.mem = s.mem → p = none → WP isa recoverInvalid t P)
    (hy : ∀ t a, VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) t → t.mem = s.mem → p = some a →
      point (env t.mem (arg s₀ 3)) 0 1 2 3 = a → WP isa next t P) :
    WP isa (decodedThen next) s P := by
  refine WP.seq (Wp.wp_test fun t ht zt => WP.block_nil ?_)
  have ht' : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) t := ⟨by rw [ht.gpr]; exact hs.edi,
    by rw [ht.gpr]; exact hs.esp, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    by rw [ht.mem]; exact hs.frame, by rw [ht.mem]; exact hs.saved⟩
  cases he : p with
  | none =>
    rw [he] at hr
    change s.gpr .eax = 0 at hr
    apply WP.ite false (by show t.zf.map (!·) = _; rw [zt, BitVec.and_self, hr]; rfl)
    · intro h; contradiction
    · intro _; exact hn t ht' ht.mem he
  | some a =>
    rw [he] at hr
    apply WP.ite true (by show t.zf.map (!·) = _; rw [zt, BitVec.and_self, hr.1]; rfl)
    · intro _; exact hy t a ht' ht.mem he (by rw [ht.mem]; exact hr.2)
    · intro h; contradiction

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.WindowLoop`. -/
section

/-!
# Verification's windows: the bytes and the loops

After the bytes of the scalars from `i` up, the sum represents
`[k / 256^i]A + [S / 256^i](-B)` (`wsum`). The bytes of `k` above its low 32
have no byte of `S` beside them (`S < 256^32`); its leading zero bytes are
skipped, where the sum is zero.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

abbrev verificationScalar (s : State) : Nat := Spec.Ed25519.decodeLE
  (Spec.Ed25519.bytesAt s.mem ((arg s 1 + BitVec.ofNat 32 32).setWidth 64) 32)
abbrev verificationChallenge (s : State) : Nat := Spec.Ed25519.decodeLE
  (Spec.Ed25519.bytesAt s.mem ((arg s 2 + BitVec.ofNat 32 0).setWidth 64) 64)

/-- Byte `i` of `k`. -/
abbrev kByte (s₀ : State) (i : Nat) : Byte :=
  (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 2 + BitVec.ofNat 32 0).setWidth 64) 64).getD i 0

/-- Byte `i` of `S`. -/
abbrev sByte (s₀ : State) (i : Nat) : Byte :=
  (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1 + BitVec.ofNat 32 32).setWidth 64) 32).getD i 0

/-- The sum after the bytes from `i` up. -/
def wsum (s₀ : State) (Aa : EPoint dZ) (i : Nat) : EPoint dZ :=
  (VG.Proof.Ed25519.X86.verificationChallenge s₀ / 256 ^ i) • Aa + (VG.Proof.Ed25519.X86.verificationScalar s₀ / 256 ^ i) • (-baseAff)

theorem kByte_val (s₀ : State) (i : Nat) :
    (VG.Proof.Ed25519.X86.kByte s₀ i).toNat = VG.Proof.Ed25519.X86.verificationChallenge s₀ / 256 ^ i % 256 := (decodeLE_byte _ i).symm

theorem sByte_val (s₀ : State) (i : Nat) :
    (VG.Proof.Ed25519.X86.sByte s₀ i).toNat = VG.Proof.Ed25519.X86.verificationScalar s₀ / 256 ^ i % 256 := (decodeLE_byte _ i).symm

theorem nib_lt16 (b : Byte) : b.toNat / 16 < 16 := by have := b.isLt; omega
theorem low_lt16 (b : Byte) : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)

/-- `k`'s digit at byte `i`, from its high (`hi`) or low nibble. -/
theorem digitK_ok {s₀ : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 64)
    (high : Bool) (t : State) (ht : WinCtx s₀ Aa R t) (et : t.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (.block (if high then digitHigh 12 0 else digitLow 12 0)) t fun u => EaxKeep t u ∧
      u.gpr .eax = BitVec.ofNat 32 (if high then (VG.Proof.Ed25519.X86.kByte s₀ i).toNat / 16 else (VG.Proof.Ed25519.X86.kByte s₀ i).toNat % 16) := by
  cases high
  · exact digitLow_ok (a := 2) ht.pre.scratch ht.saved (by decide) ht.pre.challenge hi et
  · exact digitHigh_ok (a := 2) ht.pre.scratch ht.saved (by decide) ht.pre.challenge hi et

theorem digitS_ok {s₀ : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 32)
    (high : Bool) (t : State) (ht : WinCtx s₀ Aa R t) (et : t.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (.block (if high then digitHigh 8 32 else digitLow 8 32)) t fun u => EaxKeep t u ∧
      u.gpr .eax = BitVec.ofNat 32 (if high then (VG.Proof.Ed25519.X86.sByte s₀ i).toNat / 16 else (VG.Proof.Ed25519.X86.sByte s₀ i).toNat % 16) := by
  cases high
  · exact digitLow_ok (a := 1) ht.pre.scratch ht.saved (by decide) ht.pre.scalar hi et
  · exact digitHigh_ok (a := 1) ht.pre.scratch ht.saved (by decide) ht.pre.scalar hi et

theorem nibble_lt (b : Byte) (high : Bool) : (if high then b.toNat / 16 else b.toNat % 16) < 16 := by
  cases high
  · exact VG.Proof.Ed25519.X86.low_lt16 b
  · exact VG.Proof.Ed25519.X86.nib_lt16 b

theorem windowA_byte_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {i : Nat} (hi : i < 64) (hesi : s.gpr .esi = BitVec.ofNat 32 i)
    (high : Bool) {a : EPoint dZ} (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) a) :
    WP isa (windowA (if high then digitHigh 12 0 else digitLow 12 0)) s fun t => WinCtx s₀ Aa R t ∧
      t.gpr .esi = s.gpr .esi ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3)
        ((16 : Nat) • a + (if high then (VG.Proof.Ed25519.X86.kByte s₀ i).toNat / 16 else (VG.Proof.Ed25519.X86.kByte s₀ i).toNat % 16) • Aa) :=
  windowWith_ok h (by decide) (by decide) (fun t ht => ht.ta) (VG.Proof.Ed25519.X86.nibble_lt _ high)
    (fun t ht et => VG.Proof.Ed25519.X86.digitK_ok hi high t ht (et.trans hesi)) hacc

theorem windowAB_byte_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {i : Nat} (hi : i < 32) (hesi : s.gpr .esi = BitVec.ofNat 32 i)
    (high : Bool) {a : EPoint dZ} (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) a) :
    WP isa (windowAB (if high then digitHigh 12 0 else digitLow 12 0)
        (if high then digitHigh 8 32 else digitLow 8 32)) s fun t => WinCtx s₀ Aa R t ∧
      t.gpr .esi = s.gpr .esi ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3)
        ((16 : Nat) • a + (if high then (VG.Proof.Ed25519.X86.kByte s₀ i).toNat / 16 else (VG.Proof.Ed25519.X86.kByte s₀ i).toNat % 16) • Aa +
          (if high then (VG.Proof.Ed25519.X86.sByte s₀ i).toNat / 16 else (VG.Proof.Ed25519.X86.sByte s₀ i).toNat % 16) • (-baseAff)) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.windowA_byte_ok h (by omega) hesi high hacc) fun b ⟨wb, eb, rb⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.digitS_ok hi high b wb (eb.trans hesi)) fun c ⟨kc, ec⟩ => ?_)
  have wc := wb.of_ikeep kc.ikeep (by rw [kc.mem])
  have rc : Rep (point (env c.mem (arg s₀ 3)) 0 1 2 3)
      ((16 : Nat) • a + (if high then (VG.Proof.Ed25519.X86.kByte s₀ i).toNat / 16 else (VG.Proof.Ed25519.X86.kByte s₀ i).toNat % 16) • Aa) := by
    rw [kc.mem]; exact rb
  refine WP.mono (addDigit_ok wc.ctx (by decide) (by decide) (VG.Proof.Ed25519.X86.nibble_lt _ high) ec wc.tb rc wc.d)
    fun t ⟨kt, et, rt, ht⟩ => ⟨wc.of_ikeep kt (ht 16 (by decide)), ?_, rt⟩
  rw [et, kc.gpr _ (by decide)]; exact eb

theorem esiDec_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} (h : WinCtx s₀ Aa R s)
    {i : Nat} (hesi : s.gpr .esi = BitVec.ofNat 32 (i + 1)) :
    WP isa (.block [.alu .sub .esi (.imm 1)]) s fun u => WinCtx s₀ Aa R u ∧
      u.gpr .esi = BitVec.ofNat 32 i ∧ u.mem = s.mem :=
  Wp.wp_subi fun u hu _ _ => WP.block_nil ⟨h.of_ikeep (IKeep.of_counter hu) (by rw [hu.mem]),
    by rw [hu.gpr, hesi, Wp.ofNat_pred (by omega), Nat.add_sub_cancel], hu.mem⟩

theorem test_zero (i : Nat) (hi : i < 2 ^ 32) :
    (BitVec.ofNat 32 i &&& BitVec.ofNat 32 i == 0) = decide (i = 0) := by
  rw [BitVec.and_self, Wp.ofNat_beq_zero hi]

theorem byteStepAB_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {i : Nat} (hi : i < 32) (hesi : s.gpr .esi = BitVec.ofNat 32 (i + 1))
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa (i + 1))) :
    WP isa byteStepAB s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 i ∧
      t.zf = some (decide (i = 0)) ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa i) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.esiDec_ok h hesi) fun u ⟨wu, eu, mu⟩ => ?_)
  have ru : Rep (point (env u.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa (i + 1)) := by rw [mu]; exact hacc
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.windowAB_byte_ok wu hi eu true ru) fun b ⟨wb, eb, rb⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.windowAB_byte_ok wb hi (eb.trans eu) false rb) fun c ⟨wc, ec, rc⟩ => ?_)
  refine Wp.wp_test fun t ht zt => WP.block_nil ⟨wc.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
    by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr, ec, eb, eu], ?_, ?_⟩
  · rw [zt, ec, eb, eu, VG.Proof.Ed25519.X86.test_zero i (by omega)]
  · rw [ht.mem]
    have e := window_step Aa (-baseAff) (VG.Proof.Ed25519.X86.verificationChallenge s₀) (VG.Proof.Ed25519.X86.verificationScalar s₀) i
      (VG.Proof.Ed25519.X86.kByte s₀ i) (VG.Proof.Ed25519.X86.sByte s₀ i) (VG.Proof.Ed25519.X86.kByte_val s₀ i) (VG.Proof.Ed25519.X86.sByte_val s₀ i)
    simp only [↓reduceIte, Bool.false_eq_true] at rc
    rw [VG.Proof.Ed25519.X86.wsum] at rc ⊢
    rw [← e]; exact rc

theorem byteStepA_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {i : Nat} (hi : 32 ≤ i) (hi' : i < 64)
    (hesi : s.gpr .esi = BitVec.ofNat 32 (i + 1))
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa (i + 1))) :
    WP isa byteStepA s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 i ∧
      t.zf = some (decide (i = 32)) ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa i) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.esiDec_ok h hesi) fun u ⟨wu, eu, mu⟩ => ?_)
  have ru : Rep (point (env u.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa (i + 1)) := by rw [mu]; exact hacc
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.windowA_byte_ok wu hi' eu true ru) fun b ⟨wb, eb, rb⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.windowA_byte_ok wb hi' (eb.trans eu) false rb) fun c ⟨wc, ec, rc⟩ => ?_)
  refine Wp.wp_cmpi fun t ht _ zt => WP.block_nil ⟨wc.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
    by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr, ec, eb, eu], ?_, ?_⟩
  · rw [zt, ec, eb, eu, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, Wp.sub_beq (by omega) (by omega)]
  · rw [ht.mem]
    have hS := decodeLE_lt32 s₀.mem ((arg s₀ 1 + BitVec.ofNat 32 32).setWidth 64)
    have s0 : VG.Proof.Ed25519.X86.verificationScalar s₀ / 256 ^ i = 0 := high_zero hS hi
    have s1 : VG.Proof.Ed25519.X86.verificationScalar s₀ / 256 ^ (i + 1) = 0 := high_zero hS (by omega)
    have e := window_step Aa (-baseAff) (VG.Proof.Ed25519.X86.verificationChallenge s₀) (VG.Proof.Ed25519.X86.verificationScalar s₀) i
      (VG.Proof.Ed25519.X86.kByte s₀ i) 0 (VG.Proof.Ed25519.X86.kByte_val s₀ i) (by rw [s0]; rfl)
    have z : (0 : Byte).toNat = 0 := rfl
    simp only [z, Nat.zero_div, Nat.zero_mod, s1, s0, zero_smul, add_zero] at e
    simp only [↓reduceIte, Bool.false_eq_true] at rc
    rw [VG.Proof.Ed25519.X86.wsum] at rc ⊢
    simp only [s1, s0, zero_smul, add_zero] at rc ⊢
    rw [← e]; exact rc

/-! ## The loops -/

theorem loopAB_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) (hesi : s.gpr .esi = BitVec.ofNat 32 32)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa 32)) :
    WP isa (.loop byteStepAB .ne) s fun t => WinCtx s₀ Aa R t ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa 0) := by
  refine WP.loop (M := isa) (Inv := fun m t => WinCtx s₀ Aa R t ∧ 0 < m ∧ m ≤ 32 ∧
    t.gpr .esi = BitVec.ofNat 32 m ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa m)) ?_ 32 s
    ⟨h, by decide, by decide, hesi, hacc⟩
  intro m u ⟨wu, hm0, hm, eu, ru⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.Ed25519.X86.byteStepAB_ok wu (by omega) eu ru) fun t ⟨wt, et, zt, rt⟩ => ?_
  by_cases hi : i = 0
  · subst hi
    exact .inl ⟨by show t.zf.map (!·) = _; rw [zt]; rfl, wt, rt⟩
  · exact .inr ⟨by show t.zf.map (!·) = _; rw [zt, decide_eq_false hi]; rfl, i, by omega,
      wt, by omega, by omega, et, rt⟩

theorem loopA_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {c : Nat} (hc1 : 32 < c) (hc2 : c ≤ 64)
    (hesi : s.gpr .esi = BitVec.ofNat 32 c)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa c)) :
    WP isa (.loop byteStepA .ne) s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 32 ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa 32) := by
  refine WP.loop (M := isa) (Inv := fun m t => WinCtx s₀ Aa R t ∧ 0 < m ∧ m ≤ 32 ∧
    t.gpr .esi = BitVec.ofNat 32 (32 + m) ∧
    Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa (32 + m))) ?_ (c - 32) s
    ⟨h, by omega, by omega, by rw [hesi]; congr 1; omega, by rw [show 32 + (c - 32) = c by omega]; exact hacc⟩
  intro m u ⟨wu, hm0, hm, eu, ru⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.Ed25519.X86.byteStepA_ok (i := 32 + i) wu (by omega) (by omega) eu ru) fun t ⟨wt, et, zt, rt⟩ => ?_
  by_cases hi : i = 0
  · subst hi
    exact .inl ⟨by show t.zf.map (!·) = _; rw [zt]; rfl, wt, et, rt⟩
  · exact .inr ⟨by show t.zf.map (!·) = _; rw [zt, decide_eq_false (by omega)]; rfl, i, by omega,
      wt, by omega, by omega, et, rt⟩

theorem windowsA_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {c : Nat} (hc1 : 32 ≤ c) (hc2 : c ≤ 64)
    (hesi : s.gpr .esi = BitVec.ofNat 32 c)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa c)) :
    WP isa windowsA s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 32 ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa 32) := by
  have hcmp : WP isa (.block [.alu .cmp .esi (.imm 32)]) s fun t => WinCtx s₀ Aa R t ∧
      t.gpr .esi = s.gpr .esi ∧ t.mem = s.mem ∧ t.zf = some (decide (c = 32)) :=
    Wp.wp_cmpi fun t ht _ zt => WP.block_nil ⟨h.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
      by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr], ht.mem,
      by rw [zt, hesi, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, Wp.sub_beq (by omega) (by omega)]⟩
  refine WP.seq (WP.mono hcmp fun u ⟨wu, eu, mu, zu⟩ => ?_)
  refine WP.ite (!decide (c = 32)) (by show u.zf.map (!·) = _; rw [zu]; rfl) (fun hh => ?_) (fun hh => ?_)
  · have hne : c ≠ 32 := by simpa using hh
    exact VG.Proof.Ed25519.X86.loopA_ok wu (by omega) hc2 (eu.trans hesi) (by rw [mu]; exact hacc)
  · have heq : c = 32 := by simpa using hh
    subst heq
    exact WP.block_nil ⟨wu, eu.trans hesi, by rw [mu]; exact hacc⟩

/-! ## Skipping the leading zero bytes of `k` -/

theorem skipLoad_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {c : Nat} (hc : 1 ≤ c) (hc' : c ≤ 64) (hesi : s.gpr .esi = BitVec.ofNat 32 c) :
    WP isa (.block skipLoad) s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 c ∧
      t.gpr .edx = BitVec.ofNat 32 (c - 1) ∧ t.zf = some (decide ((VG.Proof.Ed25519.X86.kByte s₀ (c - 1)).toNat = 0)) ∧
      t.mem = s.mem := by
  have hp := h.pre
  have hs := h.saved
  refine Wp.wp_mov fun u₁ h₁ => Wp.wp_subi fun u₂ h₂ _ _ => ?_
  have e₂ : u₂.gpr .edx = BitVec.ofNat 32 (c - 1) := by
    rw [h₂.gpr, h₁.gpr, hesi]; exact Wp.ofNat_pred hc
  have hsp : u₂.gpr .esp = s₀.gpr .esp := by
    rw [h₂.other _ (by decide), h₁.other _ (by decide)]; exact hs.esp
  have hr₂ : u₂.rd ++ u₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hs.rd, hs.wr]
  refine Wp.wp_ldm hsp (by rw [hr₂]; exact hp.scratch.argIn (i := 2) (by decide)) fun u₃ h₃ => ?_
  have m₂ : u₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have e₃ : u₃.gpr .eax = arg s₀ 2 := by
    rw [h₃.gpr, m₂, show (12 : Nat) = 4 + 4 * 2 from rfl]; exact hp.scratch.arg_same hs.frame (by decide)
  refine Wp.wp_add fun u₄ h₄ _ => ?_
  have e₄ : u₄.gpr .eax = arg s₀ 2 + BitVec.ofNat 32 (c - 1) := by
    rw [h₄.gpr, e₃, h₃.other .edx (by decide), e₂]
  have hA : addr (u₄.gpr .eax) 0 = addr (arg s₀ 2 + BitVec.ofNat 32 0) (c - 1) := by
    rw [e₄]; simp only [addr]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 (c - 1))]
  have hr₄ : u₄.rd ++ u₄.wr = s₀.rd ++ s₀.wr := by rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr, hr₂]
  refine scalar_ld8 hA (by rw [hr₄]; exact slice_read hp.challenge (by omega) (by decide))
    fun u₅ h₅ => Wp.wp_test fun t ht zt => WP.block_nil ?_
  have hsl := hp.challenge
  have byte : s.mem (addr (arg s₀ 2 + BitVec.ofNat 32 0) (c - 1)) = VG.Proof.Ed25519.X86.kByte s₀ (c - 1) := by
    rw [VG.Proof.Ed25519.X86.kByte, bytesAt_getD _ _ _ _ (by omega), ← addr_eq (by have := hsl.fit; omega)]
    apply hs.frame
    intro r hr; rw [List.mem_singleton.mp hr]
    exact hsl.sep _ (slice_contains hsl (by omega) (by decide))
  have mt : t.mem = s.mem := by rw [ht.mem, h₅.mem, h₄.mem, h₃.mem, m₂]
  have k₅ : IKeep (arg s₀ 3) s t := ⟨by rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide),
      h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)],
    by rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
      h₂.other _ (by decide), h₁.other _ (by decide)],
    by rw [ht.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [ht.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
    by rw [mt]; exact Frame.refl _ _⟩
  refine ⟨h.of_ikeep k₅ (by rw [mt]), ?_, ?_, ?_, mt⟩
  · rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
      h₂.other _ (by decide), h₁.other _ (by decide), hesi]
  · rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), e₂]
  · rw [zt, h₅.gpr, h₄.mem, h₃.mem, m₂, byte, BitVec.and_self]
    generalize VG.Proof.Ed25519.X86.kByte s₀ (c - 1) = b
    revert b; decide

/-- With `c` bytes of the scalars left. -/
def LoopAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (c : Nat) (t : State) : Prop :=
  WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 c ∧
    Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (VG.Proof.Ed25519.X86.wsum s₀ Aa c)

/-- Skipping, with `32 + m` bytes of `k` left, all of them above zero. -/
def SkipAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (m : Nat) (t : State) : Prop :=
  WinCtx s₀ Aa R t ∧ 0 < m ∧ m ≤ 32 ∧ t.gpr .esi = BitVec.ofNat 32 (32 + m) ∧
    VG.Proof.Ed25519.X86.verificationChallenge s₀ / 256 ^ (32 + m) = 0 ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0

/-- Whether the skipping goes on below `32 + m` bytes: the byte below is zero, and not the last
of `k` alone. -/
def skipOn (s₀ : State) (m : Nat) : Bool :=
  decide ((VG.Proof.Ed25519.X86.kByte s₀ (32 + m - 1)).toNat = 0) && decide (m ≠ 1)

/-- Where the skipping stops, if it does below `32 + m` bytes. -/
def skipEnd (s₀ : State) (m : Nat) : Nat :=
  if (VG.Proof.Ed25519.X86.kByte s₀ (32 + m - 1)).toNat = 0 then 32 + m - 1 else 32 + m

theorem wsum_zero {s₀ : State} {Aa : EPoint dZ} {c : Nat} (hc : 32 ≤ c)
    (hk : VG.Proof.Ed25519.X86.verificationChallenge s₀ / 256 ^ c = 0) : VG.Proof.Ed25519.X86.wsum s₀ Aa c = 0 := by
  rw [VG.Proof.Ed25519.X86.wsum, hk, high_zero (decodeLE_lt32 _ _) hc, zero_smul, zero_smul, add_zero]

theorem skipBody_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {m : Nat}
    (h : VG.Proof.Ed25519.X86.SkipAt s₀ Aa R m s) :
    WP isa skipBody s fun t => t.zf.map (!·) = some (VG.Proof.Ed25519.X86.skipOn s₀ m) ∧
      (VG.Proof.Ed25519.X86.skipOn s₀ m = false → 32 ≤ VG.Proof.Ed25519.X86.skipEnd s₀ m ∧ VG.Proof.Ed25519.X86.skipEnd s₀ m ≤ 64 ∧ VG.Proof.Ed25519.X86.LoopAt s₀ Aa R (VG.Proof.Ed25519.X86.skipEnd s₀ m) t) ∧
      (VG.Proof.Ed25519.X86.skipOn s₀ m = true → VG.Proof.Ed25519.X86.SkipAt s₀ Aa R (m - 1) t) := by
  obtain ⟨wu, hm0, hm, eu, ku, ru⟩ := h
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.skipLoad_ok wu (by omega) (by omega) eu) fun v ⟨wv, ev, dv, zv, mv⟩ => ?_)
  have rv : Rep (point (env v.mem (arg s₀ 3)) 0 1 2 3) 0 := by rw [mv]; exact ru
  refine WP.ite (!decide ((VG.Proof.Ed25519.X86.kByte s₀ (32 + m - 1)).toNat = 0)) (by show v.zf.map (!·) = _; rw [zv]; rfl)
    (fun hh => ?_) (fun hh => ?_)
  · have hnz : (VG.Proof.Ed25519.X86.kByte s₀ (32 + m - 1)).toNat ≠ 0 := by simpa using hh
    have son : VG.Proof.Ed25519.X86.skipOn s₀ m = false := by simp only [VG.Proof.Ed25519.X86.skipOn, decide_eq_false hnz, Bool.false_and]
    have sen : VG.Proof.Ed25519.X86.skipEnd s₀ m = 32 + m := by simp only [VG.Proof.Ed25519.X86.skipEnd, hnz, ↓reduceIte]
    refine Wp.wp_cmp fun t ht _ zt => WP.block_nil ⟨?_, fun _ => ?_, fun h => absurd h (by rw [son]; decide)⟩
    · rw [zt, son]; simp
    · rw [sen]
      refine ⟨by omega, by omega, wv.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
        by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr, ev], ?_⟩
      rw [ht.mem, VG.Proof.Ed25519.X86.wsum_zero (by omega) ku]; exact rv
  · have hz : (VG.Proof.Ed25519.X86.kByte s₀ (32 + m - 1)).toNat = 0 := by simpa using hh
    have k' : VG.Proof.Ed25519.X86.verificationChallenge s₀ / 256 ^ (32 + m - 1) = 0 := by
      have := div_split (VG.Proof.Ed25519.X86.verificationChallenge s₀) (32 + m - 1)
      rw [show 32 + m - 1 + 1 = 32 + m by omega, ku, ← VG.Proof.Ed25519.X86.kByte_val, hz] at this
      exact this
    have son : VG.Proof.Ed25519.X86.skipOn s₀ m = decide (m ≠ 1) := by
      simp only [VG.Proof.Ed25519.X86.skipOn, decide_eq_true hz, Bool.true_and]
    have sen : VG.Proof.Ed25519.X86.skipEnd s₀ m = 32 + m - 1 := by simp only [VG.Proof.Ed25519.X86.skipEnd, hz, ↓reduceIte]
    refine Wp.wp_mov fun w hw => Wp.wp_cmpi fun t ht _ zt => WP.block_nil ?_
    have ww : WinCtx s₀ Aa R t := (wv.of_ikeep (IKeep.of_counter hw) (by rw [hw.mem])).of_ikeep
      ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr, by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem])
    have et : t.gpr .esi = BitVec.ofNat 32 (32 + m - 1) := by rw [ht.gpr, hw.gpr, dv]
    have rt : Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0 := by rw [ht.mem, hw.mem]; exact rv
    have zt' : t.zf = some (decide (32 + m - 1 = 32)) := by
      rw [zt, hw.gpr, dv, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
        Wp.sub_beq (by omega) (by omega)]
    refine ⟨?_, fun hf => ?_, fun hn => ?_⟩
    · rw [zt', son]
      by_cases h1 : m = 1
      · subst h1; rfl
      · rw [decide_eq_false (show ¬(32 + m - 1 = 32) by omega), decide_eq_true h1]; rfl
    · have h1 : m = 1 := by
        rw [son] at hf
        by_contra hne
        rw [decide_eq_true hne] at hf
        cases hf
      subst h1
      rw [sen]
      exact ⟨by decide, by decide, ww, et, by rw [VG.Proof.Ed25519.X86.wsum_zero (le_refl _) k']; exact rt⟩
    · have h1 : m ≠ 1 := by
        rw [son] at hn
        exact of_decide_eq_true hn
      exact ⟨ww, by omega, by omega, by rw [et]; congr 1; omega,
        by rw [show 32 + (m - 1) = 32 + m - 1 by omega]; exact k', rt⟩

theorem skipZero_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) (hesi : s.gpr .esi = BitVec.ofNat 32 64)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) 0) :
    WP isa skipZero s fun t => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ VG.Proof.Ed25519.X86.LoopAt s₀ Aa R c t := by
  have high_zero_64 : VG.Proof.Ed25519.X86.verificationChallenge s₀ / 256 ^ (32 + 32) = 0 := Nat.div_eq_of_lt (decodeLE_lt64 _ _)
  refine WP.loop (M := isa) (Inv := fun m t => VG.Proof.Ed25519.X86.SkipAt s₀ Aa R m t) ?_ 32 s
    ⟨h, by decide, by decide, hesi, high_zero_64, hacc⟩
  intro m u hu
  have hm0 := hu.2.1
  refine WP.mono (VG.Proof.Ed25519.X86.skipBody_ok hu) fun t ⟨zt, ft, tt⟩ => ?_
  cases hs : VG.Proof.Ed25519.X86.skipOn s₀ m
  · exact .inl ⟨by show t.zf.map (!·) = _; rw [zt, hs], VG.Proof.Ed25519.X86.skipEnd s₀ m, ft hs⟩
  · exact .inr ⟨by show t.zf.map (!·) = _; rw [zt, hs], m - 1, by omega, tt hs⟩

/-! ## The whole multiplication -/

theorem Saved.frame2 {s₀ s t : State} {x : BitVec 32} (h : VG.Proof.Ed25519.X86.Saved s₀ x s) (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (hk : ScalarKeep s t) {o n o' n' : Nat} (hf : VG.Frame [VG.Proof.X25519.X86.sub x o n, VG.Proof.X25519.X86.sub x o' n'] s.mem t.mem)
    (h1 : 16 ≤ o) (h2 : o + n ≤ 8192) (h3 : 16 ≤ o') (h4 : o' + n' ≤ 8192) (h5 : o < 8192)
    (h6 : o' < 8192) : VG.Proof.Ed25519.X86.Saved s₀ x t := by
  apply h.of_frame hk hf
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [VG.Proof.X25519.X86.scR_eq]
    · exact VG.Proof.X25519.X86.sub_sub hx (Nat.zero_le _) h2 h5
    · exact VG.Proof.X25519.X86.sub_sub hx (Nat.zero_le _) h4 h6
  · intro p hp r hr
    have := VG.Proof.Ed25519.X86.savedSlots_bound p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.X25519.X86.sub_disj (by omega) (by omega) (Or.inl (by omega))
    · exact VG.Proof.X25519.X86.sub_disj (by omega) (by omega) (Or.inl (by omega))

theorem windowPrep_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s)
    {A R : Spec.Ed25519.Point} {Aa : EPoint dZ} (hA : Rep A Aa)
    (ha : tablePoint s.mem (arg s₀ 3) 7680 = A) (hr : tablePoint s.mem (arg s₀ 3) 7808 = R) :
    WP isa windowPrep s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 64 ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0 := by
  have hfit := hp.scratch.fit
  have hc := hs.ctx hfit hp.scratch.wr
  refine WP.seq (WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] hc) fun a ⟨ka, ea⟩ => ?_)
  have sa := hs.ikeep hfit (IKeep.of_field ka)
  have ca := ka.ctx hc
  have tpa : ∀ o, 928 ≤ o → o + 128 ≤ 8192 → tablePoint a.mem (arg s₀ 3) o = tablePoint s.mem (arg s₀ 3) o :=
    fun o h1 h2 => tablePoint_frame hfit ka.frame (by decide) h2 (Or.inr h1)
  refine WP.seq (WP.mono (aTable_ok ca hA (by rw [tpa 7680 (by decide) (by decide)]; exact ha)
    (by rw [ea]; rfl)) fun b hb => ?_)
  have sb := sa.frame2 hfit hb.keep hb.frame (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  refine WP.seq (WP.mono (bTable_ok hb.ctx) fun c ⟨kc, fc, tc, dc⟩ => ?_)
  have sc := sb.frame2 hfit kc fc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have cc := sc.ctx hfit hp.scratch.wr
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ cc) fun d ⟨kd, ed⟩ => ?_
  refine Wp.wp_movi fun e he => WP.block_nil ?_
  have ke : IKeep (arg s₀ 3) c e := (IKeep.of_field kd).trans (IKeep.of_counter he)
  have de : env e.mem (arg s₀ 3) 16 = env c.mem (arg s₀ 3) 16 := by rw [he.mem, ed]; rfl
  refine ⟨⟨hp, sc.ikeep hfit ke, de.trans (dc.trans hb.d), fun j hj => ?_, fun j hj => ?_, ?_⟩, he.gpr, ?_⟩
  · rw [tablePoint_frame hfit ke.frame (by decide) (by omega) (Or.inr (by omega)),
      tablePoint_frame2 fc hfit (by decide) (by decide) (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hb.table j hj
  · rw [tablePoint_frame hfit ke.frame (by decide) (by omega) (Or.inr (by omega))]
    exact tc j hj
  · rw [tablePoint_frame hfit ke.frame (by decide) (by decide) (Or.inr (by decide)),
      tablePoint_frame2 fc hfit (by decide) (by decide) (by decide) (Or.inr (by decide)) (Or.inr (by decide)),
      tablePoint_frame2 hb.frame hfit (by decide) (by decide) (by decide) (Or.inr (by decide))
        (Or.inr (by decide)), tpa 7808 (by decide) (by decide)]
    exact hr
  · rw [he.mem, ed, constPoint_eval]; exact identity_rep

theorem windowMultiply_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s)
    {A R : Spec.Ed25519.Point} {Aa : EPoint dZ} (hA : Rep A Aa)
    (ha : tablePoint s.mem (arg s₀ 3) 7680 = A) (hr : tablePoint s.mem (arg s₀ 3) 7808 = R) :
    WP isa windowMultiply s fun t => WinCtx s₀ Aa R t ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3)
        (VG.Proof.Ed25519.X86.verificationChallenge s₀ • Aa + VG.Proof.Ed25519.X86.verificationScalar s₀ • (-baseAff)) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.windowPrep_ok hp hs hA ha hr) fun e ⟨we, ee, re⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.skipZero_ok we ee re) fun f ⟨c', hc1, hc2, wf, ef, rf⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.windowsA_ok wf hc1 hc2 ef rf) fun g ⟨wg, eg, rg⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86.loopAB_ok wg eg rg) fun t ⟨wt, rt⟩ => ⟨wt, ?_⟩
  simpa only [VG.Proof.Ed25519.X86.wsum, pow_zero, Nat.div_one] using rt

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints`. -/
section

/-!
# Verification's equation from the windows

The windows' `[k]A - [S]B` equals `-R` exactly when `[S]B = R + [k]A`
(`window_equation`), which the projective comparison checks.
-/

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

theorem negR_eval (e : Env) :
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 4 5 6 7 = negPoint (point e 4 5 6 7) := rfl

theorem negR_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa (.block negR) s fun t => IKeep x s t ∧
      point (env t.mem x) 4 5 6 7 = negPoint (tablePoint s.mem x 7808) ∧
      point (env t.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
  rw [negR, WP.block_append_iff]
  refine WP.mono (pointTableQ_ok hc 7808 (by decide) (by decide)) fun a ⟨ka, _, pa, ha⟩ => ?_
  refine WP.mono (fieldCode_ok _ (ka.ctx hc)) fun t ⟨kt, et⟩ => ⟨ka.trans (IKeep.of_field kt), ?_, ?_⟩
  · rw [et, VG.Proof.Ed25519.X86.negR_eval, pa]
  · rw [et]
    change point (env a.mem x) 0 1 2 3 = _
    simp only [point, ha 0 (Or.inl (by decide)), ha 1 (Or.inl (by decide)), ha 2 (Or.inl (by decide)),
      ha 3 (Or.inl (by decide))]

theorem verifyEquationPoints_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s)
    {Aa Ra : EPoint dZ} (hA : Rep (tablePoint s.mem (arg s₀ 3) 7680) Aa)
    (hR : Rep (tablePoint s.mem (arg s₀ 3) 7808) Ra) :
    WP isa verifyEquationPoints s fun t => VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord
      (Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul (VG.Proof.Ed25519.X86.verificationScalar s₀) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem (arg s₀ 3) 7808)
          (Spec.Ed25519.pointMul (VG.Proof.Ed25519.X86.verificationChallenge s₀) (tablePoint s.mem (arg s₀ 3) 7680)))) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.windowMultiply_ok hp hs hA rfl rfl) fun u ⟨wu, ru⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.negR_ok wu.ctx) fun v ⟨kv, qv, pv⟩ => ?_)
  have sv := wu.saved.ikeep hp.scratch.fit kv
  refine WP.mono (pointEqual_ok (sv.ctx hp.scratch.fit hp.scratch.wr)) fun t ⟨kt, et⟩ =>
    ⟨sv.ikeep hp.scratch.fit (IKeep.of_field kt), ?_⟩
  rw [et, pv, qv, wu.r]
  congr 1
  exact window_equation hA hR ru.proj (hR.neg.proj)

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyDecode`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def equationResult (s : State) (a r : Spec.Ed25519.Point) : Bool :=
  Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul (VG.Proof.Ed25519.X86.verificationScalar s) Spec.Ed25519.basePoint)
    (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (VG.Proof.Ed25519.X86.verificationChallenge s) a))

def decodeRResult (s : State) (a : Spec.Ed25519.Point) : Bool :=
  match VG.Proof.Ed25519.X86.inputPoint s 1 with | none => false | some r => VG.Proof.Ed25519.X86.equationResult s a r

def decodeResult (s : State) : Bool :=
  match VG.Proof.Ed25519.X86.inputPoint s 0 with | none => false | some a => VG.Proof.Ed25519.X86.decodeRResult s a

theorem verifyDecodeR_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s)
    (hA : ∃ Aa, Rep (tablePoint s.mem (arg s₀ 3) 7680) Aa) :
    WP isa verifyDecodeR s fun t => VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) t ∧
      t.gpr .eax = signWord (VG.Proof.Ed25519.X86.decodeRResult s₀ (tablePoint s.mem (arg s₀ 3) 7680)) := by
  apply WP.assoc
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.decodeInput_ok hp.scratch hp.r hs (by decide)) fun a ht => ?_)
  have ha := ht.1
  have fa := ht.2.1
  with_reducible apply VG.Proof.Ed25519.X86.decodedThen_ok ha ht.2.2
  · intro b hb _ hn
    refine WP.mono (recoverInvalid_ok b (arg s₀ 3)) fun t ⟨kt, rt⟩ => ?_
    exact ⟨hb.ikeep hp.scratch.fit (IKeep.of_field kt), by
      rw [VG.Proof.Ed25519.X86.decodeRResult, hn]
      change t.gpr .eax = 0
      exact rt⟩
  · intro b r hb mb hr pb
    refine WP.seq (WP.mono (pointTableWrite_ok (hb.ctx hp.scratch.fit hp.scratch.wr) 7808 (by decide) (by decide))
      fun c ⟨kc, fc, pc⟩ => ?_)
    have hc := hb.of_offset hp.scratch.fit kc fc (by decide) (by decide) (by decide)
    have ca : tablePoint c.mem (arg s₀ 3) 7680 = tablePoint s.mem (arg s₀ 3) 7680 := by
      rw [tablePoint_frame hp.scratch.fit fc (by decide) (by decide) (Or.inl (by decide)), mb,
        tablePoint_frame hp.scratch.fit fa (by decide) (by decide) (Or.inr (by decide))]
    obtain ⟨Aa, hAa⟩ := hA
    obtain ⟨Ra, hRa⟩ := decodePoint_rep hr
    refine WP.mono (VG.Proof.Ed25519.X86.verifyEquationPoints_ok hp hc (by rw [ca]; exact hAa) (by rw [pc, pb]; exact hRa))
      fun t ⟨ht, vt⟩ => ?_
    refine ⟨ht, ?_⟩
    rw [vt, pc, pb, ca]
    simp only [VG.Proof.Ed25519.X86.decodeRResult, hr, VG.Proof.Ed25519.X86.equationResult]

theorem verifyDecodeA_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s) :
    WP isa verifyDecodeA s fun t => VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord (VG.Proof.Ed25519.X86.decodeResult s₀) := by
  apply WP.assoc
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.decodeInput_ok hp.scratch hp.pk hs (by decide)) fun a ht => ?_)
  have ha := ht.1
  with_reducible apply VG.Proof.Ed25519.X86.decodedThen_ok ha ht.2.2
  · intro b hb _ hn
    refine WP.mono (recoverInvalid_ok b (arg s₀ 3)) fun t ⟨kt, rt⟩ => ?_
    exact ⟨hb.ikeep hp.scratch.fit (IKeep.of_field kt), by
      rw [VG.Proof.Ed25519.X86.decodeResult, hn]
      change t.gpr .eax = 0
      exact rt⟩
  · intro b p hb _ hr pb
    refine WP.seq (WP.mono (pointTableWrite_ok (hb.ctx hp.scratch.fit hp.scratch.wr) 7680 (by decide) (by decide))
      fun c ⟨kc, fc, pc⟩ => ?_)
    have hc := hb.of_offset hp.scratch.fit kc fc (by decide) (by decide) (by decide)
    refine WP.mono (VG.Proof.Ed25519.X86.verifyDecodeR_ok hp hc (by rw [pc, pb]; exact decodePoint_rep hr)) fun t ⟨ht, vt⟩ => ?_
    exact ⟨ht, by rw [vt, pc, pb]; simp only [VG.Proof.Ed25519.X86.decodeResult, hr]⟩

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.WindowCT`. -/
section

/-!
# Verification's windows: what their traces depend on

The windows branch on the digits of the scalars and address the tables by
them, so their traces depend on the scalars: both runs must use the same ones
(in verification, the inputs are public, the same in both runs). The digits
are read through the argument pointers and the counter `esi`, the same in both
runs by correctness; everything else is public by the taint analysis, with
the workspace pointer `edi`. The skipped bytes of `k` are its leading zeros,
the same in both runs.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards
open VG.Impl.X25519.X86 (sc at_)

/-- Chains two programs: the first related, each run's state after it by correctness. -/
theorem seq_runs {P₁ P₂ F₁ F₂ : State → Prop} {Q : State → State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (fun x y => P₁ x ∧ P₂ y) c₁ (fun _ _ => True))
    (w₁ : ∀ x, P₁ x → WP isa c₁ x F₁) (w₂ : ∀ y, P₂ y → WP isa c₁ y F₂)
    (h₂ : RelCT isa (fun x y => F₁ x ∧ F₂ y) c₂ Q) :
    RelCT isa (fun x y => P₁ x ∧ P₂ y) (.seq c₁ c₂) Q :=
  VG.RelCT.seq ((h₁.wp fun x y h => ⟨w₁ x h.1, w₂ y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) h₂

theorem agree_one {r : Reg} {x y : State} (h : x.gpr r = y.gpr r) :
    VG.X86.Taint.Agree (regsTaint [r]) x y :=
  regsTaint_agree fun r' hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r'; exact h

theorem agree_two {r r' : Reg} {x y : State} (h : x.gpr r = y.gpr r ∧ x.gpr r' = y.gpr r') :
    VG.X86.Taint.Agree (regsTaint [r, r']) x y :=
  regsTaint_agree fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    exacts [h.1, h.2]

theorem agree_none {x y : State} : VG.X86.Taint.Agree (regsTaint []) x y :=
  regsTaint_agree (by simp)

theorem VerifyCTFacts.kByte {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i : Nat) :
    VG.Proof.Ed25519.X86.kByte s₀ i = VG.Proof.Ed25519.X86.kByte t₀ i :=
  congrArg (·.getD i 0) h.challengeBytes

theorem VerifyCTFacts.sByte {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i : Nat) :
    VG.Proof.Ed25519.X86.sByte s₀ i = VG.Proof.Ed25519.X86.sByte t₀ i :=
  congrArg (·.getD i 0) h.scalarBytes

theorem VerifyCTFacts.challengeNat {s t : State} (h : VerifyCTFacts s t) :
    VG.Proof.Ed25519.X86.verificationChallenge s = VG.Proof.Ed25519.X86.verificationChallenge t :=
  congrArg Spec.Ed25519.decodeLE h.challengeBytes

theorem VerifyCTFacts.scalarNat {s t : State} (h : VerifyCTFacts s t) :
    VG.Proof.Ed25519.X86.verificationScalar s = VG.Proof.Ed25519.X86.verificationScalar t :=
  congrArg Spec.Ed25519.decodeLE h.scalarBytes

theorem saved_edi {s₀ t₀ x y : State} (h : VerifyCTFacts s₀ t₀) (hx : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) x)
    (hy : VG.Proof.Ed25519.X86.Saved t₀ (arg t₀ 3) y) : x.gpr .edi = y.gpr .edi :=
  hx.edi.trans ((h.args 3 (by decide)).trans hy.edi.symm)

theorem saved_esp {s₀ t₀ x y : State} (h : VerifyCTFacts s₀ t₀) (hx : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) x)
    (hy : VG.Proof.Ed25519.X86.Saved t₀ (arg t₀ 3) y) : x.gpr .esp = y.gpr .esp :=
  hx.esp.trans (h.pub.1.trans hy.esp.symm)

/-! ## Digits -/

theorem argLoad_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s) {a : Nat}
    (ha : a < 4) :
    WP isa (.block [.mov .eax (.mem (at_ .esp (4 + 4 * a)))]) s fun u =>
      u.gpr .eax = arg s₀ a ∧ u.gpr .esi = s.gpr .esi :=
  Wp.wp_ldm hs.esp (by rw [hs.rd, hs.wr]; exact hp.argIn ha) fun u hu =>
    WP.block_nil ⟨by rw [hu.gpr]; exact hp.arg_same hs.frame ha, hu.other .esi (by decide)⟩

/-- A digit's code: the pointer's load by the taint analysis with `esp` public, the byte's by
the taint analysis with the pointer, from correctness, and the counter public. -/
theorem digit_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {P₁ P₂ : State → Prop} {a i : Nat}
    {rest : List Instr} (ha : a < 4)
    (h₁ : ∀ x, P₁ x → VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) x ∧ x.gpr .esi = BitVec.ofNat 32 i)
    (h₂ : ∀ y, P₂ y → VG.Proof.Ed25519.X86.Saved t₀ (arg t₀ 3) y ∧ y.gpr .esi = BitVec.ofNat 32 i)
    (hfirst : RelCT isa (fun x y => x.gpr .esp = y.gpr .esp)
      (.block [.mov .eax (.mem (at_ .esp (4 + 4 * a)))]) (fun _ _ => True))
    (hrest : RelCT isa (fun x y => x.gpr .eax = y.gpr .eax ∧ x.gpr .esi = y.gpr .esi)
      (.block rest) (fun _ _ => True)) :
    RelCT isa (fun x y => P₁ x ∧ P₂ y)
      (.block (([.mov .eax (.mem (at_ .esp (4 + 4 * a)))] : List Instr) ++ rest)) (fun _ _ => True) := by
  have w₁ (x : State) (hx : P₁ x) : WP isa (.block [.mov .eax (.mem (at_ .esp (4 + 4 * a)))]) x
      fun u => u.gpr .eax = arg s₀ a ∧ u.gpr .esi = BitVec.ofNat 32 i :=
    WP.mono (VG.Proof.Ed25519.X86.argLoad_ok (verify_pre h.left).scratch (h₁ x hx).1 ha) fun _ ⟨e1, e2⟩ =>
      ⟨e1, e2.trans (h₁ x hx).2⟩
  have w₂ (y : State) (hy : P₂ y) : WP isa (.block [.mov .eax (.mem (at_ .esp (4 + 4 * a)))]) y
      fun u => u.gpr .eax = arg t₀ a ∧ u.gpr .esi = BitVec.ofNat 32 i :=
    WP.mono (VG.Proof.Ed25519.X86.argLoad_ok (verify_pre h.right).scratch (h₂ y hy).1 ha) fun _ ⟨e1, e2⟩ =>
      ⟨e1, e2.trans (h₂ y hy).2⟩
  refine ctBlockAppend (((hfirst.mono (P' := fun x y => P₁ x ∧ P₂ y)
    (fun x y hh => VG.Proof.Ed25519.X86.saved_esp h (h₁ x hh.1).1 (h₂ y hh.2).1) (fun _ _ h => h)).wp
    fun x y hh => ⟨w₁ x hh.1, w₂ y hh.2⟩).mono (fun _ _ h => h) ?_) hrest
  intro x y ⟨_, ex, ey⟩
  exact ⟨ex.1.trans ((h.args a ha).trans ey.1.symm), ex.2.trans ey.2.symm⟩

theorem digitK_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {P₁ P₂ : State → Prop} {i : Nat}
    (h₁ : ∀ x, P₁ x → VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) x ∧ x.gpr .esi = BitVec.ofNat 32 i)
    (h₂ : ∀ y, P₂ y → VG.Proof.Ed25519.X86.Saved t₀ (arg t₀ 3) y ∧ y.gpr .esi = BitVec.ofNat 32 i) (high : Bool) :
    RelCT isa (fun x y => P₁ x ∧ P₂ y) (.block (if high then digitHigh 12 0 else digitLow 12 0))
      (fun _ _ => True) := by
  have first : RelCT isa (fun x y => x.gpr .esp = y.gpr .esp)
      (.block [.mov .eax (.mem (at_ .esp (4 + 4 * 2)))]) (fun _ _ => True) :=
    VG.RelCT.taint (A := taint) (regsTaint [.esp]) (fun _ _ hh => VG.Proof.Ed25519.X86.agree_one hh) (by taint_decide)
  cases high
  · show RelCT isa _ (.block ([.mov .eax (.mem (at_ .esp (4 + 4 * 2)))] ++
      [.alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax 0), .alu .and .eax (.imm 15)])) _
    exact VG.Proof.Ed25519.X86.digit_ct h (by decide) h₁ h₂ first
      (VG.RelCT.taint (A := taint) (regsTaint [.eax, .esi]) (fun _ _ hh => VG.Proof.Ed25519.X86.agree_two hh) (by taint_decide))
  · show RelCT isa _ (.block ([.mov .eax (.mem (at_ .esp (4 + 4 * 2)))] ++
      [.alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax 0), .shift .shr .eax 4])) _
    exact VG.Proof.Ed25519.X86.digit_ct h (by decide) h₁ h₂ first
      (VG.RelCT.taint (A := taint) (regsTaint [.eax, .esi]) (fun _ _ hh => VG.Proof.Ed25519.X86.agree_two hh) (by taint_decide))

theorem digitS_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {P₁ P₂ : State → Prop} {i : Nat}
    (h₁ : ∀ x, P₁ x → VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) x ∧ x.gpr .esi = BitVec.ofNat 32 i)
    (h₂ : ∀ y, P₂ y → VG.Proof.Ed25519.X86.Saved t₀ (arg t₀ 3) y ∧ y.gpr .esi = BitVec.ofNat 32 i) (high : Bool) :
    RelCT isa (fun x y => P₁ x ∧ P₂ y) (.block (if high then digitHigh 8 32 else digitLow 8 32))
      (fun _ _ => True) := by
  have first : RelCT isa (fun x y => x.gpr .esp = y.gpr .esp)
      (.block [.mov .eax (.mem (at_ .esp (4 + 4 * 1)))]) (fun _ _ => True) :=
    VG.RelCT.taint (A := taint) (regsTaint [.esp]) (fun _ _ hh => VG.Proof.Ed25519.X86.agree_one hh) (by taint_decide)
  cases high
  · show RelCT isa _ (.block ([.mov .eax (.mem (at_ .esp (4 + 4 * 1)))] ++
      [.alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax 32), .alu .and .eax (.imm 15)])) _
    exact VG.Proof.Ed25519.X86.digit_ct h (by decide) h₁ h₂ first
      (VG.RelCT.taint (A := taint) (regsTaint [.eax, .esi]) (fun _ _ hh => VG.Proof.Ed25519.X86.agree_two hh) (by taint_decide))
  · show RelCT isa _ (.block ([.mov .eax (.mem (at_ .esp (4 + 4 * 1)))] ++
      [.alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax 32), .shift .shr .eax 4])) _
    exact VG.Proof.Ed25519.X86.digit_ct h (by decide) h₁ h₂ first
      (VG.RelCT.taint (A := taint) (regsTaint [.eax, .esi]) (fun _ _ hh => VG.Proof.Ed25519.X86.agree_two hh) (by taint_decide))

/-! ## Adding a digit's entry -/

theorem digitTest_ok {s : State} {v : Nat} (hv : v < 16) {B : BitVec 32}
    (hs : s.gpr .eax = BitVec.ofNat 32 v ∧ s.gpr .edi = B) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t =>
      (t.gpr .eax = BitVec.ofNat 32 v ∧ t.gpr .edi = B) ∧ t.zf = some (decide (v = 0)) :=
  Wp.wp_test fun t ht zt => WP.block_nil ⟨⟨by rw [ht.gpr]; exact hs.1, by rw [ht.gpr]; exact hs.2⟩,
    by rw [zt, hs.1, digit_test_fact v hv]⟩

/-- A digit's addition branches on the digit and addresses the table by it, the same in both
runs. -/
theorem addDigit_ct (o : Nat) (ho : o = 1024 ∨ o = 3072) {v : Nat} (hv : v < 16) (B : BitVec 32) :
    RelCT isa (fun x y => (x.gpr .eax = BitVec.ofNat 32 v ∧ x.gpr .edi = B) ∧
      (y.gpr .eax = BitVec.ofNat 32 v ∧ y.gpr .edi = B)) (addDigit o) (fun _ _ => True) := by
  have test : RelCT isa (fun x y => (x.gpr .eax = BitVec.ofNat 32 v ∧ x.gpr .edi = B) ∧
      (y.gpr .eax = BitVec.ofNat 32 v ∧ y.gpr .edi = B)) (.block [.alu .test .eax (.reg .eax)])
      (fun _ _ => True) :=
    VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => VG.Proof.Ed25519.X86.agree_none) (by taint_decide)
  have body : RelCT isa (fun x y => x.gpr .eax = y.gpr .eax ∧ x.gpr .edi = y.gpr .edi)
      (.block (entryAddr o ++ pointFromTableQ ++ pointAdd)) (fun _ _ => True) := by
    rcases ho with rfl | rfl
    all_goals
      exact VG.RelCT.taint (A := taint) (regsTaint [.eax, .edi]) (fun _ _ hh => VG.Proof.Ed25519.X86.agree_two hh)
        (by taint_decide)
  rw [addDigit]
  refine VG.RelCT.seq ((test.wp fun x y hh => ⟨VG.Proof.Ed25519.X86.digitTest_ok hv hh.1, VG.Proof.Ed25519.X86.digitTest_ok hv hh.2⟩).mono
    (fun _ _ h => h) (fun _ _ h => h.2)) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro x y hh
    change x.zf.map Bool.not = y.zf.map Bool.not
    rw [hh.1.2, hh.2.2]
  · exact body.mono (fun x y hh => ⟨hh.1.1.1.1.trans hh.1.2.1.1.symm, hh.1.1.1.2.trans hh.1.2.1.2.symm⟩)
      (fun _ _ h => h)
  · exact VG.RelCT.block_nil fun _ _ _ => trivial

/-! ## Windows -/

/-- A window's start, in one run: the counter at `i`, and the sum representing a point. -/
def WinAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (i : Nat) (x : State) : Prop :=
  WinCtx s₀ Aa R x ∧ x.gpr .esi = BitVec.ofNat 32 i ∧
    ∃ a, Rep (point (env x.mem (arg s₀ 3)) 0 1 2 3) a

theorem doubleWindow_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i : Nat} :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x ∧ VG.Proof.Ed25519.X86.WinAt t₀ Aa R i y) doubleWindow (fun _ _ => True) :=
  VG.RelCT.taint (A := taint) (regsTaint [.edi])
    (fun _ _ hh => VG.Proof.Ed25519.X86.agree_one (VG.Proof.Ed25519.X86.saved_edi h hh.1.1.saved hh.2.1.saved)) (by taint_decide)

theorem doubleWindow_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat}
    (hx : VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x) : WP isa doubleWindow x (VG.Proof.Ed25519.X86.WinAt s₀ Aa R i) := by
  obtain ⟨w, e, a, ha⟩ := hx
  exact WP.mono (doubleWindow_ok w.ctx ha) fun b ⟨kb, eb, rb, hb⟩ =>
    ⟨w.of_ikeep kb (hb 16 (by decide)), eb.trans e, _, rb⟩

/-- After a digit's code, its value in `eax`, the workspace pointer in `edi`, and the window's
start but for `eax`. -/
def DigitAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (i v : Nat) (x : State) : Prop :=
  VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x ∧ x.gpr .eax = BitVec.ofNat 32 v ∧ x.gpr .edi = arg s₀ 3

theorem DigitAt.of_keep {s₀ x u : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i v : Nat}
    (hx : VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x) (k : EaxKeep x u) (hv : u.gpr .eax = BitVec.ofNat 32 v) :
    VG.Proof.Ed25519.X86.DigitAt s₀ Aa R i v u :=
  ⟨⟨hx.1.of_ikeep k.ikeep (by rw [k.mem]), by rw [k.gpr _ (by decide)]; exact hx.2.1,
    by rw [k.mem]; exact hx.2.2⟩, hv, by rw [k.gpr _ (by decide)]; exact hx.1.saved.edi⟩

/-- A digit's code and its addition, from the digit's value in both runs. -/
theorem digitAdd_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i v : Nat} (hv : v < 16) {digit : List Instr} {o : Nat}
    (ho : o = 1024 ∨ o = 3072)
    (hct : RelCT isa (fun x y => VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x ∧ VG.Proof.Ed25519.X86.WinAt t₀ Aa R i y) (.block digit)
      (fun _ _ => True))
    (w₁ : ∀ x, VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x → WP isa (.block digit) x (VG.Proof.Ed25519.X86.DigitAt s₀ Aa R i v))
    (w₂ : ∀ y, VG.Proof.Ed25519.X86.WinAt t₀ Aa R i y → WP isa (.block digit) y (VG.Proof.Ed25519.X86.DigitAt t₀ Aa R i v)) :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x ∧ VG.Proof.Ed25519.X86.WinAt t₀ Aa R i y) (.seq (.block digit) (addDigit o))
      (fun _ _ => True) :=
  VG.Proof.Ed25519.X86.seq_runs hct w₁ w₂ ((VG.Proof.Ed25519.X86.addDigit_ct o ho hv (arg s₀ 3)).mono
    (fun _ _ hh => ⟨⟨hh.1.2.1, hh.1.2.2⟩, ⟨hh.2.2.1, hh.2.2.2.trans (h.args 3 (by decide)).symm⟩⟩)
    (fun _ _ h => h))

theorem digitK_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 64)
    (high : Bool) (hx : VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x) :
    WP isa (.block (if high then digitHigh 12 0 else digitLow 12 0)) x
      (VG.Proof.Ed25519.X86.DigitAt s₀ Aa R i (if high then (VG.Proof.Ed25519.X86.kByte s₀ i).toNat / 16 else (VG.Proof.Ed25519.X86.kByte s₀ i).toNat % 16)) :=
  WP.mono (VG.Proof.Ed25519.X86.digitK_ok hi high x hx.1 hx.2.1) fun _ ⟨k, e⟩ => DigitAt.of_keep hx k e

theorem digitS_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 32)
    (high : Bool) (hx : VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x) :
    WP isa (.block (if high then digitHigh 8 32 else digitLow 8 32)) x
      (VG.Proof.Ed25519.X86.DigitAt s₀ Aa R i (if high then (VG.Proof.Ed25519.X86.sByte s₀ i).toNat / 16 else (VG.Proof.Ed25519.X86.sByte s₀ i).toNat % 16)) :=
  WP.mono (VG.Proof.Ed25519.X86.digitS_ok hi high x hx.1 hx.2.1) fun _ ⟨k, e⟩ => DigitAt.of_keep hx k e

theorem windowA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 64) (high : Bool) :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x ∧ VG.Proof.Ed25519.X86.WinAt t₀ Aa R i y)
      (windowA (if high then digitHigh 12 0 else digitLow 12 0)) (fun _ _ => True) := by
  rw [windowA, windowWith]
  refine VG.Proof.Ed25519.X86.seq_runs (VG.Proof.Ed25519.X86.doubleWindow_ct h) (fun _ hx => VG.Proof.Ed25519.X86.doubleWindow_at hx) (fun _ hy => VG.Proof.Ed25519.X86.doubleWindow_at hy) ?_
  refine VG.Proof.Ed25519.X86.digitAdd_ct h (VG.Proof.Ed25519.X86.nibble_lt (VG.Proof.Ed25519.X86.kByte s₀ i) high) (.inl rfl)
    (VG.Proof.Ed25519.X86.digitK_ct h (fun _ hx => ⟨hx.1.saved, hx.2.1⟩) (fun _ hy => ⟨hy.1.saved, hy.2.1⟩) high)
    (fun _ hx => VG.Proof.Ed25519.X86.digitK_at hi high hx) (fun y hy => ?_)
  rw [h.kByte i]
  exact VG.Proof.Ed25519.X86.digitK_at hi high hy

theorem windowA_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 64)
    (high : Bool) (hx : VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x) :
    WP isa (windowA (if high then digitHigh 12 0 else digitLow 12 0)) x (VG.Proof.Ed25519.X86.WinAt s₀ Aa R i) := by
  obtain ⟨w, e, a, ha⟩ := hx
  exact WP.mono (VG.Proof.Ed25519.X86.windowA_byte_ok w hi e high ha) fun _ ⟨wt, et, rt⟩ => ⟨wt, et.trans e, _, rt⟩

theorem windowAB_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 32) (high : Bool) :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x ∧ VG.Proof.Ed25519.X86.WinAt t₀ Aa R i y)
      (windowAB (if high then digitHigh 12 0 else digitLow 12 0)
        (if high then digitHigh 8 32 else digitLow 8 32)) (fun _ _ => True) := by
  rw [windowAB]
  refine VG.Proof.Ed25519.X86.seq_runs (VG.Proof.Ed25519.X86.windowA_ct h (by omega) high) (fun _ hx => VG.Proof.Ed25519.X86.windowA_at (by omega) high hx)
    (fun _ hy => VG.Proof.Ed25519.X86.windowA_at (by omega) high hy) ?_
  refine VG.Proof.Ed25519.X86.digitAdd_ct h (VG.Proof.Ed25519.X86.nibble_lt (VG.Proof.Ed25519.X86.sByte s₀ i) high) (.inr rfl)
    (VG.Proof.Ed25519.X86.digitS_ct h (fun _ hx => ⟨hx.1.saved, hx.2.1⟩) (fun _ hy => ⟨hy.1.saved, hy.2.1⟩) high)
    (fun _ hx => VG.Proof.Ed25519.X86.digitS_at hi high hx) (fun y hy => ?_)
  rw [h.sByte i]
  exact VG.Proof.Ed25519.X86.digitS_at hi high hy

theorem windowAB_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 32)
    (high : Bool) (hx : VG.Proof.Ed25519.X86.WinAt s₀ Aa R i x) :
    WP isa (windowAB (if high then digitHigh 12 0 else digitLow 12 0)
      (if high then digitHigh 8 32 else digitLow 8 32)) x (VG.Proof.Ed25519.X86.WinAt s₀ Aa R i) := by
  obtain ⟨w, e, a, ha⟩ := hx
  exact WP.mono (VG.Proof.Ed25519.X86.windowAB_byte_ok w hi e high ha) fun _ ⟨wt, et, rt⟩ => ⟨wt, et.trans e, _, rt⟩

/-! ## Bytes -/

theorem esiDec_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat}
    (hx : VG.Proof.Ed25519.X86.LoopAt s₀ Aa R (i + 1) x) : WP isa (.block [.alu .sub .esi (.imm 1)]) x (VG.Proof.Ed25519.X86.WinAt s₀ Aa R i) :=
  WP.mono (VG.Proof.Ed25519.X86.esiDec_ok hx.1 hx.2.1) fun _ ⟨w, e, m⟩ => ⟨w, e, _, by rw [m]; exact hx.2.2⟩

theorem byteStepA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 64) :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.LoopAt s₀ Aa R (i + 1) x ∧ VG.Proof.Ed25519.X86.LoopAt t₀ Aa R (i + 1) y) byteStepA
      (fun _ _ => True) := by
  rw [byteStepA]
  refine VG.Proof.Ed25519.X86.seq_runs (VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => VG.Proof.Ed25519.X86.agree_none) (by taint_decide))
    (fun _ hx => VG.Proof.Ed25519.X86.esiDec_at hx) (fun _ hy => VG.Proof.Ed25519.X86.esiDec_at hy) ?_
  refine VG.Proof.Ed25519.X86.seq_runs (VG.Proof.Ed25519.X86.windowA_ct h hi true) (fun _ hx => VG.Proof.Ed25519.X86.windowA_at hi true hx)
    (fun _ hy => VG.Proof.Ed25519.X86.windowA_at hi true hy) ?_
  refine VG.Proof.Ed25519.X86.seq_runs (F₁ := fun _ => True) (F₂ := fun _ => True) (VG.Proof.Ed25519.X86.windowA_ct h hi false)
    (fun _ hx => WP.mono (VG.Proof.Ed25519.X86.windowA_at hi false hx) fun _ _ => trivial)
    (fun _ hy => WP.mono (VG.Proof.Ed25519.X86.windowA_at hi false hy) fun _ _ => trivial) ?_
  exact VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => VG.Proof.Ed25519.X86.agree_none) (by taint_decide)

theorem byteStepAB_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 32) :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.LoopAt s₀ Aa R (i + 1) x ∧ VG.Proof.Ed25519.X86.LoopAt t₀ Aa R (i + 1) y) byteStepAB
      (fun _ _ => True) := by
  rw [byteStepAB]
  refine VG.Proof.Ed25519.X86.seq_runs (VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => VG.Proof.Ed25519.X86.agree_none) (by taint_decide))
    (fun _ hx => VG.Proof.Ed25519.X86.esiDec_at hx) (fun _ hy => VG.Proof.Ed25519.X86.esiDec_at hy) ?_
  refine VG.Proof.Ed25519.X86.seq_runs (VG.Proof.Ed25519.X86.windowAB_ct h hi true) (fun _ hx => VG.Proof.Ed25519.X86.windowAB_at hi true hx)
    (fun _ hy => VG.Proof.Ed25519.X86.windowAB_at hi true hy) ?_
  refine VG.Proof.Ed25519.X86.seq_runs (F₁ := fun _ => True) (F₂ := fun _ => True) (VG.Proof.Ed25519.X86.windowAB_ct h hi false)
    (fun _ hx => WP.mono (VG.Proof.Ed25519.X86.windowAB_at hi false hx) fun _ _ => trivial)
    (fun _ hy => WP.mono (VG.Proof.Ed25519.X86.windowAB_at hi false hy) fun _ _ => trivial) ?_
  exact VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => VG.Proof.Ed25519.X86.agree_none) (by taint_decide)

/-! ## Loops -/

theorem loopA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {c : Nat} (hc1 : 32 < c) (hc2 : c ≤ 64) :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.LoopAt s₀ Aa R c x ∧ VG.Proof.Ed25519.X86.LoopAt t₀ Aa R c y) (.loop byteStepA .ne)
      (fun x y => VG.Proof.Ed25519.X86.LoopAt s₀ Aa R 32 x ∧ VG.Proof.Ed25519.X86.LoopAt t₀ Aa R 32 y) := by
  refine (VG.RelCT.loop (I := fun m x y => (VG.Proof.Ed25519.X86.LoopAt s₀ Aa R (32 + m) x ∧ VG.Proof.Ed25519.X86.LoopAt t₀ Aa R (32 + m) y) ∧
    0 < m ∧ m ≤ 32) ?_ (c - 32)).mono
      (fun x y hh => ⟨by rw [show 32 + (c - 32) = c by omega]; exact hh, by omega, by omega⟩)
      (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ hh => Nat.lt_irrefl 0 hh.2.1
  by_cases hj : j < 32
  · have hw (u x : State) (hx : VG.Proof.Ed25519.X86.LoopAt u Aa R (32 + j + 1) x) : WP isa byteStepA x fun t =>
        t.zf.map (!·) = some (!decide (32 + j = 32)) ∧ VG.Proof.Ed25519.X86.LoopAt u Aa R (32 + j) t :=
      WP.mono (VG.Proof.Ed25519.X86.byteStepA_ok hx.1 (by omega) (by omega) hx.2.1 hx.2.2) fun t ⟨wt, et, zt, rt⟩ =>
        ⟨by rw [zt]; rfl, wt, et, rt⟩
    refine (((VG.Proof.Ed25519.X86.byteStepA_ct h (i := 32 + j) (by omega)).mono (fun x y hh => hh.1) (fun _ _ h => h)).wp
      fun x y hh => ⟨hw s₀ x hh.1.1, hw t₀ y hh.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have he' := xz.symm.trans he
      have : j = 0 := by simpa using he'
      subst this
      exact ⟨hx, hy⟩
    · have he' := xz.symm.trans he
      have : j ≠ 0 := by simpa using he'
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact VG.RelCT.of_false fun _ _ hh => hj (by omega)

theorem loopAB_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.LoopAt s₀ Aa R 32 x ∧ VG.Proof.Ed25519.X86.LoopAt t₀ Aa R 32 y) (.loop byteStepAB .ne)
      (fun _ _ => True) := by
  refine (VG.RelCT.loop (I := fun m x y => (VG.Proof.Ed25519.X86.LoopAt s₀ Aa R m x ∧ VG.Proof.Ed25519.X86.LoopAt t₀ Aa R m y) ∧
    0 < m ∧ m ≤ 32) ?_ 32).mono (fun x y hh => ⟨hh, by decide, by decide⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ hh => Nat.lt_irrefl 0 hh.2.1
  by_cases hj : j < 32
  · have hw (u x : State) (hx : VG.Proof.Ed25519.X86.LoopAt u Aa R (j + 1) x) : WP isa byteStepAB x fun t =>
        t.zf.map (!·) = some (!decide (j = 0)) ∧ VG.Proof.Ed25519.X86.LoopAt u Aa R j t :=
      WP.mono (VG.Proof.Ed25519.X86.byteStepAB_ok hx.1 hj hx.2.1 hx.2.2) fun t ⟨wt, et, zt, rt⟩ =>
        ⟨by rw [zt]; rfl, wt, et, rt⟩
    refine (((VG.Proof.Ed25519.X86.byteStepAB_ct h (i := j) hj).mono (fun x y hh => hh.1) (fun _ _ h => h)).wp
      fun x y hh => ⟨hw s₀ x hh.1.1, hw t₀ y hh.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun _ => trivial, fun he => ?_⟩
    have he' := xz.symm.trans he
    have : j ≠ 0 := by simpa using he'
    exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact VG.RelCT.of_false fun _ _ hh => hj (by omega)

theorem cmp32_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {c : Nat} (hc : c ≤ 64)
    (hx : VG.Proof.Ed25519.X86.LoopAt s₀ Aa R c x) : WP isa (.block [.alu .cmp .esi (.imm 32)]) x fun t =>
      VG.Proof.Ed25519.X86.LoopAt s₀ Aa R c t ∧ t.zf = some (decide (c = 32)) :=
  Wp.wp_cmpi fun t ht _ zt => WP.block_nil ⟨⟨hx.1.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
    by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr]; exact hx.2.1,
    by rw [ht.mem]; exact hx.2.2⟩,
    by rw [zt, hx.2.1, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, Wp.sub_beq (by omega) (by omega)]⟩

theorem windowsA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {c : Nat} (hc1 : 32 ≤ c) (hc2 : c ≤ 64) :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.LoopAt s₀ Aa R c x ∧ VG.Proof.Ed25519.X86.LoopAt t₀ Aa R c y) windowsA
      (fun x y => VG.Proof.Ed25519.X86.LoopAt s₀ Aa R 32 x ∧ VG.Proof.Ed25519.X86.LoopAt t₀ Aa R 32 y) := by
  rw [windowsA]
  refine VG.RelCT.seq ((VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => VG.Proof.Ed25519.X86.agree_none)
    (by taint_decide)).wp fun x y hh => ⟨VG.Proof.Ed25519.X86.cmp32_at hc2 hh.1, VG.Proof.Ed25519.X86.cmp32_at hc2 hh.2⟩)
    (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro x y hh
    change x.zf.map Bool.not = y.zf.map Bool.not
    rw [hh.2.1.2, hh.2.2.2]
  · by_cases hc : c = 32
    · refine VG.RelCT.of_false fun x y hh => ?_
      have e := hh.2
      change x.zf.map Bool.not = some true at e
      rw [hh.1.2.1.2, hc] at e
      simp at e
    · exact (VG.Proof.Ed25519.X86.loopA_ct h (by omega) hc2).mono (fun x y hh => ⟨hh.1.2.1.1, hh.1.2.2.1⟩) (fun _ _ h => h)
  · refine VG.RelCT.block_nil fun x y hh => ?_
    have hc : c = 32 := by
      by_contra hne
      have e := hh.2
      change x.zf.map Bool.not = some false at e
      rw [hh.1.2.1.2, decide_eq_false hne] at e
      simp at e
    subst hc
    exact ⟨hh.1.2.1.1, hh.1.2.2.1⟩

/-! ## Skipping the leading zero bytes of `k` -/

theorem skipPrefix_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s) {c : Nat}
    (hc : 1 ≤ c) (hesi : s.gpr .esi = BitVec.ofNat 32 c) :
    WP isa (.block [.mov .edx (.reg .esi), .alu .sub .edx (.imm 1), .mov .eax (.mem (at_ .esp 12))]) s
      fun t => t.gpr .eax = arg s₀ 2 ∧ t.gpr .edx = BitVec.ofNat 32 (c - 1) := by
  refine Wp.wp_mov fun u₁ h₁ => Wp.wp_subi fun u₂ h₂ _ _ => ?_
  have e₂ : u₂.gpr .edx = BitVec.ofNat 32 (c - 1) := by
    rw [h₂.gpr, h₁.gpr, hesi]; exact Wp.ofNat_pred hc
  have hsp : u₂.gpr .esp = s₀.gpr .esp := by
    rw [h₂.other _ (by decide), h₁.other _ (by decide)]; exact hs.esp
  have hr₂ : u₂.rd ++ u₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hs.rd, hs.wr]
  have m₂ : u₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine Wp.wp_ldm hsp (by rw [hr₂]; exact hp.scratch.argIn (i := 2) (by decide)) fun u₃ h₃ =>
    WP.block_nil ⟨?_, by rw [h₃.other .edx (by decide), e₂]⟩
  rw [h₃.gpr, m₂, show (12 : Nat) = 4 + 4 * 2 from rfl]
  exact hp.scratch.arg_same hs.frame (by decide)

theorem skipBody_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {m : Nat} :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.SkipAt s₀ Aa R m x ∧ VG.Proof.Ed25519.X86.SkipAt t₀ Aa R m y) skipBody (fun _ _ => True) := by
  have pre (u x : State) (hu : VerifyPre u) (hx : VG.Proof.Ed25519.X86.SkipAt u Aa R m x) :=
    VG.Proof.Ed25519.X86.skipPrefix_ok hu hx.1.saved (c := 32 + m) (by omega) hx.2.2.2.1
  have load : RelCT isa (fun x y => VG.Proof.Ed25519.X86.SkipAt s₀ Aa R m x ∧ VG.Proof.Ed25519.X86.SkipAt t₀ Aa R m y) (.block skipLoad)
      (fun _ _ => True) := by
    show RelCT isa _ (.block ([.mov .edx (.reg .esi), .alu .sub .edx (.imm 1),
      .mov .eax (.mem (at_ .esp 12))] ++ [.alu .add .eax (.reg .edx), .movzx8 .eax (at_ .eax 0),
      .alu .test .eax (.reg .eax)])) _
    refine ctBlockAppend (((VG.RelCT.taint (A := taint) (regsTaint [.esi, .esp])
      (fun x y hh => VG.Proof.Ed25519.X86.agree_two ⟨hh.1.2.2.2.1.trans hh.2.2.2.2.1.symm,
        VG.Proof.Ed25519.X86.saved_esp h hh.1.1.saved hh.2.1.saved⟩) (by taint_decide)).wp
      fun x y hh => ⟨pre s₀ x (verify_pre h.left) hh.1, pre t₀ y (verify_pre h.right) hh.2⟩).mono
        (fun _ _ h => h) fun x y hh => ⟨hh.2.1.1.trans ((h.args 2 (by decide)).trans hh.2.2.1.symm),
          hh.2.1.2.trans hh.2.2.2.symm⟩)
      (VG.RelCT.taint (A := taint) (regsTaint [.eax, .edx]) (fun _ _ hh => VG.Proof.Ed25519.X86.agree_two hh) (by taint_decide))
  have lw (u x : State) (hx : VG.Proof.Ed25519.X86.SkipAt u Aa R m x) : WP isa (.block skipLoad) x fun t =>
      t.zf = some (decide ((VG.Proof.Ed25519.X86.kByte u (32 + m - 1)).toNat = 0)) ∧
        t.gpr .edx = BitVec.ofNat 32 (32 + m - 1) :=
    WP.mono (VG.Proof.Ed25519.X86.skipLoad_ok hx.1 (by omega) (by have := hx.2.2.1; omega) hx.2.2.2.1) fun _ ⟨_, _, dt, zt, _⟩ => ⟨zt, dt⟩
  rw [skipBody]
  refine VG.RelCT.seq ((load.wp fun x y hh => ⟨lw s₀ x hh.1, lw t₀ y hh.2⟩).mono (fun _ _ h => h)
    (fun _ _ h => h.2)) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro x y hh
    change x.zf.map Bool.not = y.zf.map Bool.not
    rw [hh.1.1, hh.2.1, h.kByte]
  · exact VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => VG.Proof.Ed25519.X86.agree_none) (by taint_decide)
  · exact VG.RelCT.taint (A := taint) (regsTaint [.edx]) (fun _ _ hh => VG.Proof.Ed25519.X86.agree_one (hh.1.1.2.trans hh.1.2.2.symm))
      (by taint_decide)

theorem skipZero_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.SkipAt s₀ Aa R 32 x ∧ VG.Proof.Ed25519.X86.SkipAt t₀ Aa R 32 y) skipZero
      (fun x y => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ VG.Proof.Ed25519.X86.LoopAt s₀ Aa R c x ∧ VG.Proof.Ed25519.X86.LoopAt t₀ Aa R c y) := by
  rw [skipZero]
  refine VG.RelCT.loop (M := isa) (fun m x y => VG.Proof.Ed25519.X86.SkipAt s₀ Aa R m x ∧ VG.Proof.Ed25519.X86.SkipAt t₀ Aa R m y) ?_ 32
  intro m
  rcases m with _ | m
  · exact VG.RelCT.of_false fun _ _ hh => Nat.lt_irrefl 0 hh.1.2.1
  refine ((VG.Proof.Ed25519.X86.skipBody_ct h).wp fun x y hh => ⟨VG.Proof.Ed25519.X86.skipBody_ok hh.1, VG.Proof.Ed25519.X86.skipBody_ok hh.2⟩).mono
    (fun _ _ h => h) ?_
  intro x y ⟨_, ⟨xz, xf, xt⟩, ⟨yz, yf, yt⟩⟩
  have es : VG.Proof.Ed25519.X86.skipOn t₀ (m + 1) = VG.Proof.Ed25519.X86.skipOn s₀ (m + 1) := by rw [VG.Proof.Ed25519.X86.skipOn, VG.Proof.Ed25519.X86.skipOn, h.kByte]
  have ee : VG.Proof.Ed25519.X86.skipEnd t₀ (m + 1) = VG.Proof.Ed25519.X86.skipEnd s₀ (m + 1) := by rw [VG.Proof.Ed25519.X86.skipEnd, VG.Proof.Ed25519.X86.skipEnd, h.kByte]
  refine ⟨?_, fun he => ?_, fun he => ?_⟩
  · change x.zf.map (!·) = y.zf.map (!·)
    rw [xz, yz, es]
  · have hs : VG.Proof.Ed25519.X86.skipOn s₀ (m + 1) = false := Option.some.inj (xz.symm.trans he)
    obtain ⟨c1, c2, lx⟩ := xf hs
    obtain ⟨_, _, ly⟩ := yf (es.trans hs)
    exact ⟨VG.Proof.Ed25519.X86.skipEnd s₀ (m + 1), c1, c2, lx, ee ▸ ly⟩
  · have hs : VG.Proof.Ed25519.X86.skipOn s₀ (m + 1) = true := Option.some.inj (xz.symm.trans he)
    exact ⟨m, by omega, xt hs, yt (es.trans hs)⟩

/-! ## The whole multiplication -/

/-- Before the equation's points: the saved state, `A` at byte 7680 and `R` at byte 7808. -/
def EquationCTPre (s₀ : State) (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s ∧ tablePoint s.mem (arg s₀ 3) 7680 = a ∧ tablePoint s.mem (arg s₀ 3) 7808 = r

theorem windowMultiply_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {a r : Spec.Ed25519.Point}
    {Aa : EPoint dZ} (hA : Rep a Aa) :
    RelCT isa (fun x y => VG.Proof.Ed25519.X86.EquationCTPre s₀ a r x ∧ VG.Proof.Ed25519.X86.EquationCTPre t₀ a r y) windowMultiply
      (fun _ _ => True) := by
  have prep : RelCT isa (fun x y => VG.Proof.Ed25519.X86.EquationCTPre s₀ a r x ∧ VG.Proof.Ed25519.X86.EquationCTPre t₀ a r y) windowPrep
      (fun _ _ => True) :=
    VG.RelCT.taint (A := taint) (regsTaint [.edi]) (fun _ _ hh => VG.Proof.Ed25519.X86.agree_one (VG.Proof.Ed25519.X86.saved_edi h hh.1.1 hh.2.1))
      (by taint_decide)
  have pw (u x : State) (hu : VerifyPre u) (hx : VG.Proof.Ed25519.X86.EquationCTPre u a r x) :
      WP isa windowPrep x (VG.Proof.Ed25519.X86.SkipAt u Aa r 32) :=
    WP.mono (VG.Proof.Ed25519.X86.windowPrep_ok hu hx.1 hA hx.2.1 hx.2.2) fun _ ⟨w, e, rp⟩ =>
      ⟨w, by decide, by decide, e, Nat.div_eq_of_lt (decodeLE_lt64 _ _), rp⟩
  rw [windowMultiply]
  refine VG.Proof.Ed25519.X86.seq_runs prep (fun x hx => pw s₀ x (verify_pre h.left) hx)
    (fun y hy => pw t₀ y (verify_pre h.right) hy) ?_
  refine VG.RelCT.seq (VG.Proof.Ed25519.X86.skipZero_ct h) ?_
  refine VG.RelCT.exists_ (M := isa)
    (P := fun c x y => 32 ≤ c ∧ c ≤ 64 ∧ VG.Proof.Ed25519.X86.LoopAt s₀ Aa r c x ∧ VG.Proof.Ed25519.X86.LoopAt t₀ Aa r c y) fun c => ?_
  by_cases hc : 32 ≤ c ∧ c ≤ 64
  · exact VG.RelCT.seq ((VG.Proof.Ed25519.X86.windowsA_ct h hc.1 hc.2).mono (fun _ _ hh => hh.2.2) (fun _ _ h => h))
      ((VG.Proof.Ed25519.X86.loopAB_ct h).mono (fun _ _ h => h) (fun _ _ _ => trivial))
  · exact VG.RelCT.of_false fun _ _ hh => hc ⟨hh.1, hh.2.1⟩

end VG.Proof.Ed25519.X86

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyCTEquation`. -/
section

/-!
# Verification's equation: what its traces depend on

The windows' traces depend only on the public scalars (`windowMultiply_ct`), and the projective
comparison's on whether the points represented are equal (`pointEqualRep_ct`), the same in both
runs.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

private theorem ctEqualOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := ⟨rfl, rfl, rfl, rfl⟩

theorem equalFirst_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.X86.Ctx base s) :
    WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
      FieldKeep base s t ∧
      t.zf = some (decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2)) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.ctx hs) 8 9) fun t ⟨kt, te, tz⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_, ?_⟩
  · rw [tz, va, (ctEqualOps_eval _).1, (ctEqualOps_eval _).2.1]
  · rw [te 10 (by decide), va, (ctEqualOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (ctEqualOps_eval _).2.2.2]

theorem returnFlag_ct (b : Bool) :
    RelCT isa (fun _ _ => True) (.block [.mov .eax (.imm (if b then 1 else 0))]) (fun _ _ => True) := by
  cases b
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)

/-- Two points representing `P` and `Q` in slots 0–3 and 4–7. -/
def EqRepPre (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) (s : State) : Prop :=
  VG.Proof.Ed25519.X86.Ctx base s ∧ VG.Proof.Ed25519.RepP (point (env s.mem base) 0 1 2 3) P ∧
    VG.Proof.Ed25519.RepP (point (env s.mem base) 4 5 6 7) Q

/-- The comparison branches on whether the points represented are equal. -/
theorem pointEqualRep_ct (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) :
    RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      Impl.Ed25519.X86.pointEqual (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : EqRepPre base P Q s) :
      WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
        VG.Proof.Ed25519.X86.Ctx base t ∧ t.zf = some (decide (P.x = Q.x)) ∧
          (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y) := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ⟨kt.ctx h.1, ?_, ?_⟩
    · rw [tz]
      exact congrArg some (decide_eq_decide.mpr (VG.Proof.Ed25519.repP_cross_x h.2.1 h.2.2))
    · rw [tu, tv]
      exact VG.Proof.Ed25519.repP_cross_y h.2.1 h.2.2
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have ht2 : RelCT isa (fun s t => (VG.Proof.Ed25519.X86.Ctx base s ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) ∧
      (VG.Proof.Ed25519.X86.Ctx base t ∧ (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y)))
      (.block (fieldEqual 10 11)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw2 (s : State) (h : VG.Proof.Ed25519.X86.Ctx base s ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) :
      WP isa (.block (fieldEqual 10 11)) s fun t => t.zf = some (decide (P.y = Q.y)) :=
    WP.mono (fieldEqual_ok h.1 10 11) fun t k => by
      rw [k.2.2]; exact congrArg some (decide_eq_decide.mpr h.2)
  have hp2 := VG.RelCT.wp ht2 (fun s t h => ⟨hw2 s h.1, hw2 t h.2⟩)
  rw [Impl.Ed25519.X86.pointEqual]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · refine VG.RelCT.seq (hp2.mono (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩)
      (fun _ _ h => h)) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
    · exact fun _ _ h => h.2.1.trans h.2.2.symm
    · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

/-- The windows, `-R`, and the comparison: the windows' traces depend only on the public
scalars, and the comparison's on whether the points represented are equal. -/
theorem verifyEquationPoints_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a r : Spec.Ed25519.Point)
    {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    RelCT isa (fun s t => EquationCTPre s₀ a r s ∧ EquationCTPre t₀ a r t) verifyEquationPoints
      (fun _ _ => True) := by
  have ww (u x : State) (hu : VerifyPre u) (hx : EquationCTPre u a r x) :=
    windowMultiply_ok hu hx.1 hA hx.2.1 hx.2.2
  have nw (u x : State) (hx : WinCtx u Aa r x ∧ Rep (point (env x.mem (arg u 3)) 0 1 2 3)
      (verificationChallenge u • Aa + verificationScalar u • (-baseAff))) :
      WP isa (.block negR) x
        (EqRepPre (arg u 3) (verificationChallenge u • Aa + verificationScalar u • (-baseAff)) (-Ra)) :=
    WP.mono (negR_ok hx.1.ctx) fun t ⟨kt, qt, pt⟩ =>
      ⟨kt.ctx hx.1.ctx, by rw [pt]; exact hx.2.proj, by rw [qt, hx.1.r]; exact hR.neg.proj⟩
  rw [verifyEquationPoints]
  refine seq_runs (windowMultiply_ct h hA) (fun x hx => ww s₀ x (verify_pre h.left) hx)
    (fun y hy => ww t₀ y (verify_pre h.right) hy) ?_
  refine seq_runs (VG.RelCT.taint (A := taint) (regsTaint [.edi])
    (fun _ _ hh => agree_one (saved_edi h hh.1.1.saved hh.2.1.saved)) (by taint_decide))
    (fun x hx => nw s₀ x hx) (fun y hy => nw t₀ y hy) ?_
  refine (pointEqualRep_ct (arg s₀ 3) (verificationChallenge s₀ • Aa + verificationScalar s₀ • (-baseAff))
    (-Ra)).mono (fun x y hh => ⟨hh.1, ?_⟩) (fun _ _ h => h)
  rw [h.args 3 (by decide), h.challengeNat, h.scalarNat]
  exact hh.2

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyVerified`. -/
section

/-! Merged from `Proof.Ed25519.X86.VerifyMain`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verificationScalar_num {s : State} (hp : VerifyPre s) :
    verificationScalar s = VG.Proof.X25519.X86.fe s.mem (arg s 1 + 32) 0 := by
  rw [verificationScalar, ← VG.Proof.X25519.X86.addr_zero (arg s 1 + BitVec.ofNat 32 32)]
  exact decode_words s.mem 8 (by have := hp.scalar.fit; omega_using [this])

private theorem verification_order (pk sig ch : List Byte)
    (hp : pk.length = 32) (hs : sig.length = 64) (hc : ch.length = 64) :
    Spec.Ed25519.verifyEquation pk sig ch =
      (decide (Spec.Ed25519.decodeLE (sig.drop 32) < Spec.Ed25519.L) &&
        (match Spec.Ed25519.decodePoint pk with
        | none => false
        | some a => match Spec.Ed25519.decodePoint (sig.take 32) with
          | none => false
          | some r => Spec.Ed25519.pointEqual
            (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (sig.drop 32)) Spec.Ed25519.basePoint)
            (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE ch) a)))) := by
  rw [Spec.Ed25519.verifyEquation, hp, hs, hc]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  cases Spec.Ed25519.decodePoint pk <;> cases Spec.Ed25519.decodePoint (sig.take 32) <;>
    simp only [Bool.and_false]

theorem verifyEquation_result {s : State} (hp : VerifyPre s) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
      (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64) =
      (decide (verificationScalar s < Spec.Ed25519.L) && decodeResult s) := by
  have address : (arg s 1 + BitVec.ofNat 32 32).setWidth 64 = (arg s 1).setWidth 64 + BitVec.ofNat 64 32 :=
    addr_eq (by have hf := hp.signature_fit; omega_using [hf])
  rw [verification_order _ _ _
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]),
    signatureBytes_take, signatureBytes_drop, ← address]
  have zero (i : Nat) : arg s i + BitVec.ofNat 32 0 = arg s i := BitVec.add_zero _
  simp only [decodeResult, decodeRResult, inputPoint, equationResult, verificationScalar,
    verificationChallenge, zero]

theorem verifyBody_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s) :
    WP isa (.seq (.block verifyScalar) (.ite .e verifyDecodeA recoverInvalid)) s fun t =>
      VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord
        (decide (verificationScalar s₀ < Spec.Ed25519.L) && decodeResult s₀) := by
  refine WP.seq (WP.mono (verifyScalar_ok hp.scratch hp.scalar hs) fun a ⟨ha, za⟩ => ?_)
  rw [← verificationScalar_num hp] at za
  apply WP.ite (decide (verificationScalar s₀ < Spec.Ed25519.L)) za
  · intro hh
    refine WP.mono (verifyDecodeA_ok hp ha) fun t ⟨ht, vt⟩ => ⟨ht, ?_⟩
    rw [hh, Bool.true_and]
    exact vt
  · intro hh
    refine WP.mono (recoverInvalid_ok a (arg s₀ 3)) fun t ⟨kt, rt⟩ => ?_
    exact ⟨ha.ikeep hp.scratch.fit (IKeep.of_field kt), by rw [hh, Bool.false_and]; exact rt⟩

theorem verify_correct {s : State} (h : verifyLocal.pre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  have hp := verify_pre h
  refine WP.seq (WP.mono (abiSave_ok hp.scratch) fun a ha => ?_)
  refine WP.seq (WP.mono (verifyBody_ok hp ha) fun b ⟨hb, vb⟩ => ?_)
  refine WP.mono (verifyFinish_ok hp.scratch hb) fun t ⟨abi_t, vt, _⟩ => ⟨abi_t, ?_⟩
  change t.gpr .eax = _
  rw [vt, vb, verifyEquation_result hp]

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.VerifyCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyCTDecode`. -/
section
/-! Merged from `Proof.Ed25519.X86.DecodedThenCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyCTDecodeInput`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem inputSliceValue_ok {s₀ s : State} {i : Nat} (hp : ScratchPre s₀ 3 4)
    (hi : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 0) 32)
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s) (hia : i < 4) :
    WP isa (.block (inputSliceWords i 0 96 8)) s fun t => VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) t ∧
      VG.Proof.X25519.X86.fe t.mem (arg s₀ 3) 96 = Spec.Ed25519.decodeLE
        (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32) := by
  refine WP.mono (inputSliceWords_ok hp hi hs hia (by decide) (by decide) (by decide)) fun t ⟨ht, wt, _⟩ => ?_
  refine ⟨ht, ?_⟩
  rw [← VG.Proof.X25519.X86.addr_zero (arg s₀ i + BitVec.ofNat 32 0), decode_words s₀.mem 8 (by have := hi.fit; omega_using [this])]
  apply VG.Proof.X25519.X86.num_congr
  intro k hk
  simp only [Nat.zero_add]
  exact congrArg BitVec.toNat (wt k hk)

theorem decodeInput_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i : Nat) (hi : i ≤ 2)
    (is : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 0) 32)
    (it : SlicePre t₀ 3 (arg t₀ i + BitVec.ofNat 32 0) 32)
    (hb : Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t₀.mem ((arg t₀ i + BitVec.ofNat 32 0).setWidth 64) 32) :
    RelCT isa (VerifySaved s₀ t₀) (.seq (.block (inputSliceWords i 0 96 8)) pointDecode) (fun _ _ => True) := by
  have hh := (inputSlice96_ct h i hi).wp (fun _ _ hp =>
    ⟨inputSliceValue_ok (verify_pre h.left).scratch is hp.1 (by omega),
      inputSliceValue_ok (verify_pre h.right).scratch it hp.2 (by omega)⟩)
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_)
    (pointDecode_ct (arg s₀ 3) (Spec.Ed25519.decodeLE
      (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32)))
  intro s t hp
  have hs := hp.2.1
  have ht := hp.2.2
  have left : DecodeCTPre (arg s₀ 3) _ s :=
    ⟨hs.1.ctx (verify_pre h.left).scratch.fit (verify_pre h.left).scratch.wr, hs.2⟩
  have right : DecodeCTPre (arg t₀ 3) (Spec.Ed25519.decodeLE
      (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32)) t :=
    ⟨ht.1.ctx (verify_pre h.right).scratch.fit (verify_pre h.right).scratch.wr,
      ht.2.trans (congrArg Spec.Ed25519.decodeLE hb.symm)⟩
  exact ⟨left, Eq.mp (congrArg (fun base => DecodeCTPre base
    (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32)) t)
    (h.args 3 (by decide)).symm) right⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure TestUnchanged (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Saved.test {s₀ s t : State} {base : BitVec 32} (h : VG.Proof.Ed25519.X86.Saved s₀ base s) (k : TestUnchanged s t) : VG.Proof.Ed25519.X86.Saved s₀ base t :=
  ⟨(congrFun k.gpr _).trans h.edi, (congrFun k.gpr _).trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr,
    by rw [k.mem]; exact h.frame, by rw [k.mem]; exact h.saved⟩

theorem DecodeResult.test {base : BitVec 32} {p : Option Spec.Ed25519.Point} {s t : State}
    (h : DecodeResult base p s) (k : TestUnchanged s t) : DecodeResult base p t := by
  cases p with
  | none => exact (congrFun k.gpr _).trans h
  | some p => exact ⟨(congrFun k.gpr _).trans h.1, by rw [k.mem]; exact h.2⟩

theorem decodedThen_ct (base : BitVec 32) (p : Option Spec.Ed25519.Point) (P₁ P₂ : State → Prop) (next : Prog isa)
    (hP₁ : ∀ s t, TestUnchanged s t → P₁ s → P₁ t)
    (hP₂ : ∀ s t, TestUnchanged s t → P₂ s → P₂ t)
    (hn : ∀ a, p = some a → RelCT isa
      (fun s t => (P₁ s ∧ point (env s.mem base) 0 1 2 3 = a) ∧
        (P₂ t ∧ point (env t.mem base) 0 1 2 3 = a)) next (fun _ _ => True)) :
    RelCT isa (fun s t => (P₁ s ∧ DecodeResult base p s) ∧ (P₂ t ∧ DecodeResult base p t))
      (decodedThen next) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => (P₁ s ∧ DecodeResult base p s) ∧ (P₂ t ∧ DecodeResult base p t))
      (.block [.alu .test .eax (.reg .eax)]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)
  have hw (P : State → Prop) (hP : ∀ s t, TestUnchanged s t → P s → P t) (s : State)
      (h : P s ∧ DecodeResult base p s) :
      WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t => P t ∧ DecodeResult base p t ∧ t.zf = some (!p.isSome) := by
    refine Wp.wp_test fun t kt zt => WP.block_nil ?_
    have k : TestUnchanged s t := ⟨kt.gpr, kt.mem, kt.rd, kt.wr⟩
    refine ⟨hP s t k h.1, h.2.test k, ?_⟩
    rw [zt, BitVec.and_self, decodeResult_flag h.2]
    cases p <;> rfl
  have hp := ht.wp (fun s t h => ⟨hw P₁ hP₁ s h.1, hw P₂ hP₂ t h.2⟩)
  rw [decodedThen]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t h
    change s.zf.map Bool.not = t.zf.map Bool.not
    rw [h.2.1.2.2, h.2.2.2.2]
  · cases p with
    | none =>
      apply VG.RelCT.of_false
      intro s t h
      have he := h.2
      change s.zf.map Bool.not = some true at he
      rw [h.1.2.1.2.2] at he
      contradiction
    | some a =>
      exact (hn a rfl).mono
        (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.1.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem VerifyCTFacts.inputA {s t : State} (h : VerifyCTFacts s t) : inputPoint s 0 = inputPoint t 0 :=
  congrArg Spec.Ed25519.decodePoint h.pkBytes

theorem VerifyCTFacts.inputR {s t : State} (h : VerifyCTFacts s t) : inputPoint s 1 = inputPoint t 1 :=
  congrArg Spec.Ed25519.decodePoint h.rBytes

def DecodeRCTPre (s₀ : State) (a : Spec.Ed25519.Point) (s : State) : Prop :=
  VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s ∧ tablePoint s.mem (arg s₀ 3) 7680 = a

theorem pointTableWrite_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (o : Nat) (ho : o = 7680 ∨ o = 7808) :
    RelCT isa (VerifySaved s₀ t₀) (.block (pointTableWrite o)) (fun _ _ => True) := by
  rcases ho with rfl | rfl
  all_goals
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  all_goals exact fun _ _ hp => regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
    (hp.1.edi.trans ((h.args 3 (by decide)).trans hp.2.edi.symm)))

theorem verifyStoreR_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a r : Spec.Ed25519.Point)
    {Aa Ra : Edwards.EPoint VG.Proof.Ed25519.dZ} (hA : VG.Proof.Ed25519.Rep a Aa)
    (hR : VG.Proof.Ed25519.Rep r Ra) :
    RelCT isa (fun s t => (DecodeRCTPre s₀ a s ∧ point (env s.mem (arg s₀ 3)) 0 1 2 3 = r) ∧
      (DecodeRCTPre t₀ a t ∧ point (env t.mem (arg s₀ 3)) 0 1 2 3 = r))
      (.seq (.block (pointTableWrite 7808)) verifyEquationPoints) (fun _ _ => True) := by
  have hc := (pointTableWrite_ct h 7808 (Or.inr rfl)).mono
    (P' := fun (s t : State) => (DecodeRCTPre s₀ a s ∧ point (env s.mem (arg s₀ 3)) 0 1 2 3 = r) ∧
      (DecodeRCTPre t₀ a t ∧ point (env t.mem (arg s₀ 3)) 0 1 2 3 = r))
    (fun _ _ hp => ⟨hp.1.1.1, hp.2.1.1⟩) (fun _ _ h => h)
  have hw (u s : State) (hu : VerifyPre u) (hs : DecodeRCTPre u a s)
      (hr : point (env s.mem (arg u 3)) 0 1 2 3 = r) :
      WP isa (.block (pointTableWrite 7808)) s (EquationCTPre u a r) := by
    refine WP.mono (pointTableWrite_ok (hs.1.ctx hu.scratch.fit hu.scratch.wr) 7808 (by decide) (by decide))
      fun t ⟨kt, ft, pt⟩ => ?_
    refine ⟨hs.1.of_offset hu.scratch.fit kt ft (by decide) (by decide) (by decide), ?_, pt.trans hr⟩
    exact (tablePoint_frame hu.scratch.fit ft (by decide) (by decide) (Or.inl (by decide))).trans hs.2
  have hh := hc.wp (fun s t hp => ⟨hw s₀ s (verify_pre h.left) hp.1.1 hp.1.2,
    hw t₀ t (verify_pre h.right) hp.2.1 ((h.args 3 (by decide)) ▸ hp.2.2)⟩)
  exact VG.RelCT.seq (hh.mono (fun _ _ h => h) (fun _ _ h => h.2)) (verifyEquationPoints_ct h a r hA hR)

theorem verifyDecodeR_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a : Spec.Ed25519.Point)
    {Aa : Edwards.EPoint VG.Proof.Ed25519.dZ} (hA : VG.Proof.Ed25519.Rep a Aa) :
    RelCT isa (fun s t => DecodeRCTPre s₀ a s ∧ DecodeRCTPre t₀ a t) verifyDecodeR (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have hc := (decodeInput_ct h 1 (by decide) ps.r pt.r h.rBytes).mono
    (P' := fun (s t : State) => DecodeRCTPre s₀ a s ∧ DecodeRCTPre t₀ a t)
    (fun _ _ hp => ⟨hp.1.1, hp.2.1⟩) (fun _ _ h => h)
  have hw (u s : State) (hu : VerifyPre u) (hs : DecodeRCTPre u a s) :
      WP isa (.seq (.block (inputSliceWords 1 0 96 8)) pointDecode) s fun t =>
        DecodeRCTPre u a t ∧ DecodeResult (arg u 3) (inputPoint u 1) t := by
    refine WP.mono (decodeInput_ok hu.scratch hu.r hs.1 (by decide)) fun t ht => ?_
    have ha := (tablePoint_frame hu.scratch.fit ht.2.1 (by decide) (by decide) (Or.inr (by decide))).trans hs.2
    have hpre : DecodeRCTPre u a t := ⟨ht.1, ha⟩
    with_reducible exact ⟨hpre, ht.2.2⟩
  have hh := hc.wp (fun s t hp => ⟨hw s₀ s ps hp.1, hw t₀ t pt hp.2⟩)
  rw [verifyDecodeR]
  apply VG.RelCT.assoc
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_)
    (decodedThen_ct (arg s₀ 3) (inputPoint s₀ 1) (DecodeRCTPre s₀ a) (DecodeRCTPre t₀ a)
      (.seq (.block (pointTableWrite 7808)) verifyEquationPoints) ?_ ?_ ?_)
  · intro s t hp
    with_reducible refine ⟨hp.2.1, hp.2.2.1, ?_⟩
    with_reducible exact Eq.mp (congrArg₂ (fun base p => DecodeResult base p t)
      (h.args 3 (by decide)).symm h.inputR.symm) hp.2.2.2
  · intro s t k hp
    exact ⟨hp.1.test k, by rw [k.mem]; exact hp.2⟩
  · intro s t k hp
    exact ⟨hp.1.test k, by rw [k.mem]; exact hp.2⟩
  · intro r hr
    obtain ⟨Ra, hRa⟩ := VG.Proof.Ed25519.decodePoint_rep hr
    exact verifyStoreR_ct h a r hA hRa

theorem verifyStoreA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a : Spec.Ed25519.Point)
    {Aa : Edwards.EPoint VG.Proof.Ed25519.dZ} (hA : VG.Proof.Ed25519.Rep a Aa) :
    RelCT isa (fun s t => (VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s ∧ point (env s.mem (arg s₀ 3)) 0 1 2 3 = a) ∧
      (VG.Proof.Ed25519.X86.Saved t₀ (arg t₀ 3) t ∧ point (env t.mem (arg s₀ 3)) 0 1 2 3 = a))
      (.seq (.block (pointTableWrite 7680)) verifyDecodeR) (fun _ _ => True) := by
  have hc := (pointTableWrite_ct h 7680 (Or.inl rfl)).mono
    (P' := fun (s t : State) => (VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s ∧ point (env s.mem (arg s₀ 3)) 0 1 2 3 = a) ∧
      (VG.Proof.Ed25519.X86.Saved t₀ (arg t₀ 3) t ∧ point (env t.mem (arg s₀ 3)) 0 1 2 3 = a))
    (fun _ _ hp => ⟨hp.1.1, hp.2.1⟩) (fun _ _ h => h)
  have hw (u s : State) (hu : VerifyPre u) (hs : VG.Proof.Ed25519.X86.Saved u (arg u 3) s)
      (ha : point (env s.mem (arg u 3)) 0 1 2 3 = a) :
      WP isa (.block (pointTableWrite 7680)) s (DecodeRCTPre u a) := by
    refine WP.mono (pointTableWrite_ok (hs.ctx hu.scratch.fit hu.scratch.wr) 7680 (by decide) (by decide))
      fun t ⟨kt, ft, pt⟩ => ?_
    exact ⟨hs.of_offset hu.scratch.fit kt ft (by decide) (by decide) (by decide), pt.trans ha⟩
  have hh := hc.wp (fun s t hp => ⟨hw s₀ s (verify_pre h.left) hp.1.1 hp.1.2,
    hw t₀ t (verify_pre h.right) hp.2.1 ((h.args 3 (by decide)) ▸ hp.2.2)⟩)
  exact VG.RelCT.seq (hh.mono (fun _ _ h => h) (fun _ _ h => h.2)) (verifyDecodeR_ct h a hA)

theorem verifyDecodeA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀) verifyDecodeA (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have hh := ctWithRuns (decodeInput_ct h 0 (by decide) ps.pk pt.pk h.pkBytes)
    (fun _ _ hp => ⟨decodeInput_ok ps.scratch ps.pk hp.1 (by decide),
      decodeInput_ok pt.scratch pt.pk hp.2 (by decide)⟩)
  rw [verifyDecodeA]
  apply VG.RelCT.assoc
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_)
    (decodedThen_ct (arg s₀ 3) (inputPoint s₀ 0) (VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3)) (VG.Proof.Ed25519.X86.Saved t₀ (arg t₀ 3))
      (.seq (.block (pointTableWrite 7680)) verifyDecodeR) ?_ ?_ ?_)
  · intro s t ⟨_, _, _, _, hs, ht⟩
    with_reducible refine ⟨⟨hs.1, hs.2.2⟩, ht.1, ?_⟩
    with_reducible exact Eq.mp (congrArg₂ (fun base p => DecodeResult base p t)
      (h.args 3 (by decide)).symm h.inputA.symm) ht.2.2
  · intro s t k hp; exact hp.test k
  · intro s t k hp; exact hp.test k
  · intro a ha
    obtain ⟨Aa, hAa⟩ := VG.Proof.Ed25519.decodePoint_rep ha
    exact verifyStoreA_ct h a hAa

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.VerifyCTSetup`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def verifyEntryTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 20 }

theorem verifyEntryTaint_wf {s : State} (h : verifyLocal.pre s) : VG.X86.Taint.Wf verifyEntryTaint s := by
  have hp := (verify_pre h).scratch
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (by cases h),
    fun _ h => (by cases h), fun _ => ⟨?_, ?_⟩, fun _ h => (by cases h)⟩
  · exact hp.sp_fit
  · intro r hr
    rw [h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro a _ ha
      change _ + 1 ≤ 0 at ha
      omega_using [ha]
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.sp_fit; omega_using [this]) hp.ret_sc hp.args_sc

theorem verifyEntryTaint_agree {s t : State} (h : VerifyCTFacts s t) : VG.X86.Taint.Agree verifyEntryTaint s t := by
  refine ⟨⟨?_, fun h => (by cases h)⟩, fun h => absurd rfl h,
    verifyEntryTaint_wf h.left, verifyEntryTaint_wf h.right,
    fun _ h => (by cases h), fun _ h => (by cases h), fun _ => h.pub.1, ?_⟩
  · intro r hr
    simp only [verifyEntryTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r
    exact h.pub.1
  · intro k h4 hk
    change k < 20 at hk
    rw [show VG.X86.Taint.depth verifyEntryTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (verify_pre h.left).scratch.sp_fit h4 hk,
      VG.X86.Taint.argByte_eq (verify_pre h.right).scratch.sp_fit h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (h.args ((k - 4) / 4) (by omega_using [hk, h4]))

theorem verifyStart_ct : RelCT isa
    (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
    (.block (abiSave 3)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) verifyEntryTaint _ (by taint_decide)
  exact fun _ _ h => verifyEntryTaint_agree ⟨h.1, h.2.1, h.2.2⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verifyBody_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀) (.seq (.block verifyScalar) (.ite .e verifyDecodeA recoverInvalid))
      (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have hh := (verifyScalar_ct h).wp (fun _ _ hp =>
    ⟨verifyScalar_ok ps.scratch ps.scalar hp.1, verifyScalar_ok pt.scratch pt.scalar hp.2⟩)
  refine VG.RelCT.seq hh (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t hp
    change s.zf = t.zf
    rw [hp.2.1.2, hp.2.2.2, h.scalarFe]
  · exact (verifyDecodeA_ct h).mono (fun _ _ hp => ⟨hp.1.2.1.1, hp.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem verifyTail_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀)
      (.seq (.seq (.block verifyScalar) (.ite .e verifyDecodeA recoverInvalid)) (.block verifyFinish))
      (fun _ _ => True) := by
  have hh := (verifyBody_ct h).wp (fun _ _ hp =>
    ⟨verifyBody_ok (verify_pre h.left) hp.1, verifyBody_ok (verify_pre h.right) hp.2⟩)
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_) verifyFinish_ct
  intro s t hp
  exact hp.2.1.1.edi.trans ((h.args 3 (by decide)).trans hp.2.2.1.edi.symm)

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have start := ctWithRuns verifyStart_ct (fun _ _ h =>
    ⟨abiSave_ok (verify_pre h.1).scratch, abiSave_ok (verify_pre h.2.1).scratch⟩)
  rw [verifyEquation]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact verifyTail_ct ⟨hp.1, hp.2.1, hp.2.2⟩ _ _ _ _ _ _ ⟨hu, hv⟩ es et

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.VerifyNarrow`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyWide`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def verifyWide : Contract isa :=
  { verifyLocal with
  pre := fun s =>
    let pk := VG.Proof.X25519.X86.sub (arg s 0) 0 32
    let sig := VG.Proof.X25519.X86.sub (arg s 1) 0 64
    let challenge := VG.Proof.X25519.X86.sub (arg s 2) 0 64
    let scratch := VG.Proof.X25519.X86.scR 8192 (arg s 3)
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [pk, sig, challenge] ∧ s.wr = [scratch, args] ∧
      pk.Disjoint scratch ∧ sig.Disjoint scratch ∧ challenge.Disjoint scratch ∧
      args.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

def verifyRd (s : State) : List Region :=
  [VG.Proof.X25519.X86.sub (arg s 0) 0 32, VG.Proof.X25519.X86.sub (arg s 1) 0 64, VG.Proof.X25519.X86.sub (arg s 2) 0 64, ⟨argAddr s 0, 16⟩]
def verifyWr (s : State) : List Region := [VG.Proof.X25519.X86.sub (arg s 3) 0 0, VG.Proof.X25519.X86.scR 8192 (arg s 3)]

theorem verifyWide_pre (s : State) (h : verifyWide.pre s) :
    verifyLocal.pre (s.withRegions (verifyRd s) (verifyWr s)) := by
  simp only [verifyLocal, verifyRd, verifyWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

def verifySatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else
    if a = 0x800d then 0x30 else if a = 0x8011 then 0x40 else 0

def verifySatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := verifySatMem
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8004, 16⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verifyWide_implies : verifyWide.Implies (Spec.Ed25519.verifyEquationContract X86.abi) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyWide, verifyLocal, VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    change t.gpr .eax = signWord _ at h
    rw [h, BitVec.setWidth_append_eq_right]
    generalize Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
      (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨sp, bytes, pk, sig, challenge, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    exact ⟨sp, pk, sig, challenge, base, first, middle, last⟩
  sat := by
    have a0 : arg verifySatState 0 = 0x1000 := by decide
    have a1 : arg verifySatState 1 = 0x2000 := by decide
    have a2 : arg verifySatState 2 = 0x3000 := by decide
    have a3 : arg verifySatState 3 = 0x4000 := by decide
    have e : argAddr verifySatState 0 = 0x8004 := by decide
    have esp : verifySatState.gpr .esp = 0x8000 := rfl
    sig_implies_sat [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyWide, verifyLocal, VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, e, esp] using verifySatState

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86

theorem verifyNarrow_read (s : State) (h : verifyWide.pre s) (a : Addr) (n : Nat)
    (hr : InRegions (verifyRd s ++ verifyWr s) a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := hr
  rw [h.1, h.2.1]
  simp only [verifyRd, verifyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl)
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩
  · refine ⟨VG.Proof.X25519.X86.scR 8192 (arg s 3), by simp, ?_⟩
    simp only [VG.Proof.X25519.X86.addr_zero, Region.Contains] at hc ⊢
    omega_using [hc]
  · exact ⟨_, by simp, hc⟩

theorem verifyNarrow_write (s : State) (h : verifyWide.pre s) (a : Addr) (n : Nat)
    (hr : InRegions (verifyWr s) a n) : InRegions s.wr a n := by
  obtain ⟨r, hr, hc⟩ := hr
  rw [h.2.1]
  simp only [verifyWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨VG.Proof.X25519.X86.scR 8192 (arg s 3), by simp, ?_⟩
    simp only [VG.Proof.X25519.X86.addr_zero, Region.Contains] at hc ⊢
    omega_using [hc]
  · exact ⟨_, by simp, hc⟩

end VG.Proof.Ed25519.X86
end

/-! Transfer the verifier from its framed local contract to the reviewed ABI. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verify_verified_of_correct
    (correct : ∀ s, verifyLocal.pre s → WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t)
    (ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation) :
    Verified X86.target verifyEquation (Spec.Ed25519.verifyEquationContract X86.abi) := by
  have hsat := verifyWide_implies.sat_left
  have satLocal : ∃ s, verifyLocal.pre s := hsat.elim fun s h => ⟨_, verifyWide_pre s h⟩
  have verifiedLocal : Verified X86.target verifyEquation verifyLocal :=
    Verified.of_correct correct ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal verifyRd verifyWr verifyWide_pre
    verifyNarrow_read verifyNarrow_write ?_ ?_ hsat) verifyWide_implies
  · intro s t _ h
    simpa only [verifyWide, verifyLocal, arg_withRegions, State.withRegions_mem, State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [verifyWide, verifyLocal, arg_withRegions, State.withRegions_gpr, State.withRegions_mem] using h

theorem verify_verified : Verified X86.target verifyEquation
    (Spec.Ed25519.verifyEquationContract X86.abi) :=
  verify_verified_of_correct (fun _ h => verify_correct h) verify_ct

end VG.Proof.Ed25519.X86

end
