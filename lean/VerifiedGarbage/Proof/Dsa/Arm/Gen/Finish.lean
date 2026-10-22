module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.SLoop
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Pre
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: the exit

`finish_vp`: p‖q‖g copied from `sPacked` to `out` and 1 returned when the
search found them (`fStatus` = 1), else `out` zeroed and 0 returned (`FO`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.WriteBytes
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_movw wp_dp wp_subs wp_strb op2_imm eval_eq eval_ne
  ofNat_beq_zero)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.Rsa.Arm.Keys (seqs)

/-- After the exit, the frame still allocated: `out` holds the result, `r0`
the status. -/
structure FO (G : GP) (R : Option Spec.Dsa.Params) (σ t : State) : Prop where
  pre : CIn σ
  hG : mkG σ = G
  sp : t.sp = G.sp
  rd : t.rd = σ.rd
  wr : t.wr = G.rFrame :: σ.wr
  saved : Spill.Saved t.mem (State.addr G.sp) σ.gpr saved
  frame : Frame (G.rOut :: G.chg) σ.mem t.mem
  out : Spec.Rsa.bytesAt t.mem (State.addr G.out) G.outLen =
    (R.map (Spec.Dsa.encodeParams G.pLen G.qLen)).getD (List.replicate G.outLen 0)
  r0 : t.gpr .r0 = BitVec.ofNat 32 (if R.isSome then 1 else 0)

section
variable {G : GP} {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} {X : State → Prop}

theorem GI.frame_out (h : GI G σ V LS s) : G.rFrame.Disjoint G.rOut := by
  rw [← h.hG]; exact h.pre.fO.sub_left (by rw [h.hG]; exact h.frameSub)

theorem GI.outLen (h : GI G σ V LS s) : G.outLen = 2 * G.pLen + G.qLen := by
  rw [← h.hG]; exact h.pre.outLen

theorem GI.outFit (h : GI G σ V LS s) : G.out.toNat + G.outLen ≤ 2 ^ 32 := by
  rw [← h.hG]; exact h.pre.nO

theorem GI.outW (h : GI G σ V LS s) : G.rOut ∈ s.wr := by
  rw [h.wr, h.pre.wr, h.hG]; simp

/-- A state of the search, then writes to `out` alone. -/
theorem GI.fo {t : State} {ws : List Reg} {R : Option Spec.Dsa.Params} (h : GI G σ V LS s) (r : Rest ws s t)
    (f : Frame [G.rOut] s.mem t.mem)
    (ho : Spec.Rsa.bytesAt t.mem (State.addr G.out) G.outLen =
      (R.map (Spec.Dsa.encodeParams G.pLen G.qLen)).getD (List.replicate G.outLen 0))
    (h0 : t.gpr .r0 = BitVec.ofNat 32 (if R.isSome then 1 else 0)) : FO G R σ t := by
  refine ⟨h.pre, h.hG, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, fun p hp => ?_,
    (h.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans (f.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self), ho, h0⟩
  have hb : p.2 + 4 ≤ F := by
    simp only [VG.Impl.Dsa.Arm.Generation.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  show fw t.mem G p.2 = _
  rw [frame_readW f (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.frame_out) hb]
  exact h.saved p hp

end

/-! ## Zeroing `out` -/

theorem wp_inc {is : List Instr} {s : State} {Q : State → Prop} {d : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d + 1) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d d (.imm 1) :: is)) s Q :=
  wp_dp (op2_imm (by decide)) k

theorem wp_dec {is : List Instr} {s : State} {Q : State → Prop} {d : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - 1) → s'.z = (s.gpr d - 1 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d d (.imm 1) :: is)) s Q :=
  wp_subs (op2_imm (by decide)) k

theorem ofNat32_sub_one {k : Nat} (hk : 1 ≤ k) : BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (1 : BitVec 32).toNat = 1 from rfl]
  omega

/-- `k` bytes from `p` zeroed. -/
structure ZI (t : State) (p : BitVec 32) (N k : Nat) (u : State) : Prop where
  r0 : u.gpr .r0 = p + BitVec.ofNat 32 k
  lr : u.gpr .lr = BitVec.ofNat 32 (N - k)
  mem : u.mem = writeBytes t.mem (State.addr p) (List.replicate k 0)
  rest : Rest [.r0, .lr] t u

theorem zeroLoop_ok {t : State} {p : BitVec 32} {N : Nat} (hN : 0 < N) (hfit : p.toNat + N ≤ 2 ^ 32)
    (hw : ∀ k < N, InRegions t.wr (State.addr p + BitVec.ofNat 64 k) 1) (r0 : t.gpr .r0 = p)
    (r3 : t.gpr .r3 = 0) (lr : t.gpr .lr = BitVec.ofNat 32 N) :
    WP isa (.loop (.block zeroStep) .ne) t fun u =>
      u.mem = writeBytes t.mem (State.addr p) (List.replicate N 0) ∧ Rest [.r0, .lr] t u := by
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ k, n = N - k ∧ k < N ∧ ZI t p N k u)
    (fun n u hu => ?_) _ t ⟨0, rfl, hN, ⟨by rw [r0, BitVec.add_zero], by rw [lr, Nat.sub_zero],
      by rw [List.replicate_zero, writeBytes_nil], Rest.refl _ _⟩⟩
  obtain ⟨k, rfl, hk, I⟩ := hu
  unfold zeroStep
  refine wp_strb (a := State.addr p + BitVec.ofNat 64 k) (by decide)
    (by rw [BitVec.add_zero, I.r0, addr_add (by omega)]) (by rw [I.rest.wr]; exact hw k hk) fun u₁ m₁ =>
    wp_inc fun u₂ v₂ => wp_dec fun u₃ v₃ z₃ => WP.block_nil ?_
  have R : Rest [.r0, .lr] u u₃ := (m₁.rest _).trans ((v₂.rest (by simp)).trans (v₃.rest (by simp)))
  have J : ZI t p N (k + 1) u₃ := by
    refine ⟨?_, ?_, ?_, I.rest.trans R⟩
    · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.r0, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.lr, ofNat32_sub_one (by omega)]; rfl
    · have h3 : (u.gpr .r3).setWidth 8 = 0 := by rw [I.rest.gpr _ (by decide), r3]; rfl
      rw [v₃.mem, v₂.mem, m₁.mem, h3, I.mem, List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega),
        List.length_replicate]
  have hz : u₃.z = decide (N - (k + 1) = 0) := by
    rw [z₃, v₂.other _ (by decide), m₁.gpr, I.lr, ofNat32_sub_one (by omega), ofNat_beq_zero (by omega),
      Nat.sub_sub]
  by_cases he : N - (k + 1) = 0
  · left
    refine ⟨by rw [eval_ne, hz, decide_eq_true he]; rfl, ?_, J.rest⟩
    rw [J.mem, show k + 1 = N by omega]
  · right
    exact ⟨by rw [eval_ne, hz, decide_eq_false he]; rfl, _, by omega, k + 1, rfl, by omega, J⟩

/-! ## The two exits -/

section
variable {G : GP} {X : State → Prop}

/-- No parameters: `out` zeroed, 0 returned. -/
theorem outZero_vp {g : Geo} {c : Cfg} {F : State → State → Prop} (hF : ∀ σ s, F σ s → St G c X σ s)
    (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) :
    VP F (seqs [.block [ld .r0 fOut], .block [.mov .r3 (.imm 0), .movw .lr (BitVec.ofNat 16 (2 * g.pLen + g.qLen))],
      .loop (.block zeroStep) .ne, .block [.mov .r0 (.imm 0)]]) (fun σ t => FO G none σ t ∧ X σ) := by
  refine VP.seq (G := fun σ t => ∃ s, St G c X σ s ∧ Upd s t .r0 G.out)
    (ld_vp (o := fOut) (fun σ s h => (hF σ s h).1) (by decide) (by decide)
      (fun σ s h => (hF σ s h).1.fixedV (by simp [fixedWords])) fun σ s t h u => ⟨s, hF σ s h, u⟩) ?_
  refine VP.taint [.r0] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0])
      (seqs [.block [.mov .r3 (.imm 0), .movw .lr (BitVec.ofNat 16 5)],
        .loop (.block zeroStep) .ne, .block [.mov .r0 (.imm 0)]]), rfl⟩ (fun σ₁ σ₂ s₁ s₂ ⟨_, _, u₁⟩ ⟨_, _, u₂⟩ r hr => ?_) fun σ t ⟨s, ⟨h, x⟩, u⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [u₁.gpr, u₂.gpr]
  have gi := h.gi
  have hol := gi.outLen
  have fit := gi.outFit
  have hN : 0 < G.outLen := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  have h16 : G.outLen < 2 ^ 16 := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  refine WP.seq (wp_mov (op2_imm (by decide)) fun t₁ u₁ => wp_movw fun t₂ u₂ => WP.block_nil ?_)
  refine WP.seq (WP.mono (zeroLoop_ok (t := t₂) (p := G.out) hN fit (fun k hk => ⟨G.rOut, ?_, ?_⟩) ?_ ?_ ?_)
    fun t₃ ⟨m₃, R₃⟩ => wp_mov (op2_imm (by decide)) fun t₄ u₄ => WP.block_nil ?_)
  · rw [u₂.wr, u₁.wr, u.wr]; exact gi.outW
  · exact Offset.contains_base _ (by omega) (by omega)
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), u.gpr]
  · rw [u₂.other _ (by decide), u₁.gpr]
  · rw [u₂.gpr]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hL, hQ]; omega
  have R : Rest [.r0, .r3, .lr] s t₄ := (u.rest (by simp)).trans ((u₁.rest (by simp)).trans
    ((u₂.rest (by simp)).trans ((R₃.mono (by simp)).trans (u₄.rest (by simp)))))
  have m₄ : t₄.mem = writeBytes s.mem (State.addr G.out) (List.replicate G.outLen 0) := by
    rw [u₄.mem, m₃, u₂.mem, u₁.mem, u.mem]
  refine ⟨gi.fo R ?_ ?_ (by rw [u₄.gpr]; rfl), x⟩
  · rw [m₄]; exact writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
  · rw [m₄]
    have := bytesAt_writeBytes s.mem (State.addr G.out) (List.replicate G.outLen 0) (d := 0) (k := G.outLen)
      (by simp) (by simp; omega)
    rw [BitVec.add_zero] at this
    rw [this]; simp

/-- Parameters at `sPacked`: copied to `out`, 1 returned. -/
theorem outCopy_vp {g : Geo} {c : Cfg} {a : Spec.Dsa.Params} {F : State → State → Prop}
    (hF : ∀ σ s, F σ s → St G c X σ s) (hcl : (sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a) ∈ c.cl)
    (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) :
    VP F (seqs [.block [ld .r0 fOut], .block (scr g.pLen .r1 sPacked ++ ([.movw .lr (BitVec.ofNat 16 (2 * g.pLen + g.qLen))] : List Instr)),
      VG.Impl.Bignum.Arm.copyBytes, .block [.mov .r0 (.imm 1)]]) (fun σ t => FO G (some a) σ t ∧ X σ) := by
  -- After the pointers and the count.
  let P₂ : State → State → Prop := fun σ t => ∃ s, St G c X σ s ∧ Rest [.r0, .r1, .r12, .lr] s t ∧
    t.mem = s.mem ∧ t.gpr .r0 = G.out ∧ t.gpr .r1 = G.scr + BitVec.ofNat 32 sPacked ∧
    t.gpr .lr = BitVec.ofNat 32 G.outLen
  -- After the copy.
  let P₃ : State → State → Prop := fun σ t => ∃ s, St G c X σ s ∧ Rest [.r0, .r1, .r2, .r12, .lr] s t ∧
    Frame [G.rOut] s.mem t.mem ∧ Spec.Rsa.bytesAt t.mem (State.addr G.out) G.outLen =
      Spec.Dsa.encodeParams G.pLen G.qLen a
  have hlen := VG.Proof.Dsa.Generation.encodeParams_length G.pLen G.qLen a
  refine VP.seq (G := fun σ t => ∃ s, St G c X σ s ∧ Upd s t .r0 G.out)
    (ld_vp (o := fOut) (fun σ s h => (hF σ s h).1) (by decide) (by decide)
      (fun σ s h => (hF σ s h).1.fixedV (by simp [fixedWords])) fun σ s t h u => ⟨s, hF σ s h, u⟩)
    (VP.seq (G := P₂) ?_ (VP.seq (G := P₃) ?_ ?_))
  · refine VP.taint [.r0, .r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r8])
        (.block (scr 128 .r1 0 ++ [.movw .lr (BitVec.ofNat 16 5)])), rfl⟩ (fun σ₁ σ₂ s₁ s₂ ⟨_, h₁, u₁⟩ ⟨_, h₂, u₂⟩ r hr => ?_) fun σ t ⟨s, ⟨h, x⟩, u⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [u₁.gpr, u₂.gpr]
      · rw [u₁.other _ (by decide), u₂.other _ (by decide), h₁.1.r8, h₂.1.r8]
    have gi := h.gi
    have hol := gi.outLen
    have h16 : G.outLen < 2 ^ 16 := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    have hpk : sPacked ≤ sK G.pLen := by
      have := h.clOk _ hcl; dsimp only at this; omega
    refine scr_ok (d := .r1) (by rw [u.other _ (by decide)]; exact h.r8) hL (hL ▸ h.lens) (hL ▸ hpk)
      fun s₁ v₁ R₁ M₁ => wp_movw fun s₂ u₂ => WP.block_nil
        ⟨s, ⟨h, x⟩, (u.rest (by simp)).trans ((R₁.mono (by simp)).trans (u₂.rest (by simp))),
          by rw [u₂.mem, M₁, u.mem], by rw [u₂.other _ (by decide), R₁.gpr _ (by decide), u.gpr],
          by rw [u₂.other _ (by decide)]; exact v₁, ?_⟩
    rw [u₂.gpr]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hL, hQ]; omega
  · refine copyBytes_vp (src := G.scr + BitVec.ofNat 32 sPacked) (dst := G.out) (n := G.outLen)
      (fun σ t ⟨_, _, _, _, a, b, c⟩ => ⟨b, a, c⟩) fun σ s₂ ⟨s, ⟨h, x⟩, R, M, v0, v1, vl⟩ => ?_
    have gi := h.gi
    have hol := gi.outLen
    have big := gi.scrBig
    have fit := gi.scrFit
    have ofit := gi.outFit
    have hN : 0 < G.outLen := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    have h16 : G.outLen < 2 ^ 16 := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    have hpk : sPacked + G.outLen ≤ sK G.pLen := by
      have := h.clOk _ hcl; dsimp only at this; omega
    have ad := h.addr hpk hN
    have oc := gi.pre.oC
    rw [gi.hG] at oc
    refine WP.mono (VG.Proof.Bignum.Arm.copyBuffer_ok s₂ hN (by rw [h.toNat (by omega)]; omega) ofit (by omega)
      (by rw [ad, R.rd, R.wr]; obtain ⟨r, hr, hc⟩ := gi.inScr (o := sPacked) (n := G.outLen) (by omega)
          exact ⟨r, List.mem_append_right _ hr, hc⟩)
      ⟨G.rOut, by rw [R.wr]; exact gi.outW, Region.contains_self _ _⟩
      (by rw [ad]; exact oc.symm.sub_left (sw G (by omega))) v0 v1 vl)
      fun t ⟨rd', fr, _, rest⟩ => ⟨s, ⟨h, x⟩, (R.mono (by simp)).trans (rest.mono (by simp)), by rw [← M]; exact fr, ?_⟩
    rw [bytesAt_of_read rd', M, ad, hol, ← hlen]
    have e := h.sb _ hcl; dsimp only at e; exact e
  · refine VP.taint [] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs []) (.block [.mov .r0 (.imm 1)]), rfl⟩
      (fun _ _ _ _ _ _ r hr => absurd hr (by simp)) fun σ t ⟨s, ⟨h, x⟩, R, fr, ho⟩ =>
      wp_mov (op2_imm (by decide)) fun t' u => WP.block_nil ⟨h.gi.fo (R.trans (u.rest (by simp)))
        (by rw [u.mem]; exact fr) (by rw [u.mem, ho]; rfl) (by rw [u.gpr]; rfl), x⟩

/-- The exit. -/
theorem finish_vp {g : Geo} (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) (R : Option Spec.Dsa.Params) :
    VP (St G (sFin G R) X) g.finish (fun σ t => FO G R σ t ∧ X σ) := by
  unfold Geo.finish
  cases R with
  | none =>
    refine VP.seq (G := fun σ s => St G (sFin G none) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [sFin])).trans (by simp [sFin]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    exact VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
      (outZero_vp (fun σ s h => h.1.1) hL hQ)
  | some a =>
    refine VP.seq (G := fun σ s => St G (sFin G (some a)) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [sFin])).trans (by simp [sFin]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    exact VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (outCopy_vp (fun σ s h => h.1.1) (by simp [sFin]) hL hQ)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)

end

end VG.Proof.Dsa.Arm.Gen
