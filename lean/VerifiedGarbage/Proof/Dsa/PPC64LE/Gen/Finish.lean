module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.SLoop
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Entry
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Pre
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Frame
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter generation on PPC64LE: the exit

`finish_vp`: p‖q‖g copied from `sPacked` to `out` and 1 returned when the
search found them (`fStatus` = 1), else `out` zeroed and 0 returned (`FO`).
`FO.restore`: then our caller's registers back.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.WriteBytes
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

/-- After the exit: `out` holds the result, `r3` the status, and the header
our caller's registers. -/
structure FO (G : GP) (R : Option Spec.Dsa.Params) (σ t : State) : Prop where
  pre : CIn 176 σ
  hG : mkG σ = G
  sp : t.sp = σ.sp
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  r28 : t.gpr .r28 = G.scr
  saved : ∀ i < 19, fw t.mem G (fSave + 8 * i) = σ.gpr (saved.getD i .r14)
  lr : fw t.mem G fLR = σ.lr
  frame : Frame [G.rOut, G.rScr, rBelow σ 176] σ.mem t.mem
  out : Spec.Rsa.bytesAt t.mem G.out G.outLen =
    (R.map (Spec.Dsa.encodeParams G.pLen G.qLen)).getD (List.replicate G.outLen 0)
  r3 : t.gpr .r3 = BitVec.ofNat 64 (if R.isSome then 1 else 0)

section
variable {G : GP} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat} {X : State → Prop}

theorem GI.outLen (h : GI G 176 σ V LS s) : G.outLen = 2 * G.pLen + G.qLen := by
  rw [← h.hG]; exact h.pre.outLen

theorem GI.outFit (h : GI G 176 σ V LS s) : G.out.toNat + G.outLen ≤ 2 ^ 64 := by
  rw [← h.hG]; exact h.pre.nO

theorem GI.outW (h : GI G 176 σ V LS s) : G.rOut ∈ s.wr := by
  rw [h.wr, h.pre.wr, h.hG]; simp

theorem GI.out_scr (h : GI G 176 σ V LS s) : G.rOut.Disjoint G.rScr := by
  rw [← h.hG]; exact h.pre.oC

/-- A state of the search, then writes to `out` alone. -/
theorem GI.fo {t : State} {ws : List Reg} {R : Option Spec.Dsa.Params} (h : GI G 176 σ V LS s) (K : Keep ws s t)
    (sp : t.sp = s.sp) (f : Frame [G.rOut] s.mem t.mem)
    (ho : Spec.Rsa.bytesAt t.mem G.out G.outLen =
      (R.map (Spec.Dsa.encodeParams G.pLen G.qLen)).getD (List.replicate G.outLen 0))
    (h3 : t.gpr .r3 = BitVec.ofNat 64 (if R.isSome then 1 else 0)) (h28 : .r28 ∉ ws := by decide) : FO G R σ t := by
  have hE := h.hEnd_le
  have hd : ∀ o, o + 8 ≤ hEnd → ∀ r ∈ [G.rOut], (G.rs o 8).Disjoint r := fun o ho r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact h.out_scr.symm.sub_left (sw G (by omega))
  refine ⟨h.pre, h.hG, sp.trans h.sp, K.2.1.trans h.rd, K.2.2.trans h.wr, (K.gpr h28).trans h.r28,
    fun i hi => ?_, ?_, (h.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans (f.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self), ho, h3⟩
  · rw [fw_frame f (hd _ (by simp only [hEnd] at hE ⊢; omega))]; exact h.saved i hi
  · rw [fw_frame f (hd _ (by decide))]; exact h.lr

/-- After the exit, `restore`. -/
theorem FO.restore {R : Option Spec.Dsa.Params} {t : State} (h : FO G R σ t) :
    WP isa (.block restore) t fun u => abiPreserved σ u ∧ u.mem = t.mem ∧ u.gpr .r3 = t.gpr .r3 := by
  have big : 8 * (64 * G.pLen + 1024) ≤ G.scrLen * 8 := by
    have := h.pre.scrLen
    have e1 : (σ.gpr .r5).toNat = G.pLen := by rw [← h.hG]; rfl
    have e2 : (stackArg σ 3).toNat = G.scrLen := by rw [← h.hG]; rfl
    rw [e1, e2] at this
    simp only [Spec.Dsa.generationScratchWords] at this
    omega
  have fit : G.scr.toNat + G.scrLen * 8 ≤ 2 ^ 64 := by have := h.pre.nC; rw [← h.hG]; exact this
  refine restore_ok' h.r28 h.saved h.lr h.sp fun o ho => ?_
  refine ⟨G.rScr, List.mem_append_right _ (by rw [h.wr, h.pre.wr, h.hG]; simp), Offset.contains_base _ ?_ ?_⟩ <;>
    simp only [hEnd, fSave] at ho <;> omega

end

/-! ## Zeroing `out` -/

/-- `k` bytes from `P` zeroed. -/
structure ZI (t : State) (P : Addr) (N k : Nat) (u : State) : Prop where
  r3 : u.gpr .r3 = P + BitVec.ofNat 64 k
  r5 : u.gpr .r5 = BitVec.ofNat 64 (N - k)
  r0 : u.gpr .r0 = 0
  keep : Keep [.r3, .r5] t u
  sp : u.sp = t.sp
  mem : u.mem = writeBytes t.mem P (List.replicate k 0)

theorem zeroLoop_ok {t : State} {P : Addr} {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 64) (hfit : P.toNat + N ≤ 2 ^ 64)
    (hw : ∀ k < N, InRegions t.wr (P + BitVec.ofNat 64 k) 1) (r3 : t.gpr .r3 = P) (r0 : t.gpr .r0 = 0)
    (r5 : t.gpr .r5 = BitVec.ofNat 64 N) :
    WP isa (.loop (.block [.stb .r0 .r3 0, .addi .r3 .r3 1, .subi .r5 .r5 1]) (.nonzero .d .r5)) t fun u =>
      Keep [.r3, .r5] t u ∧ u.sp = t.sp ∧ u.mem = writeBytes t.mem P (List.replicate N 0) := by
  refine loop_nz (ZI t P N) hN (fun k hk u I => ?_) (fun u I => ⟨I.keep, I.sp, I.mem⟩)
    ⟨by rw [r3]; simp, by rw [r5]; simp, r0, Keep.refl _ _, rfl, by rw [List.replicate_zero, writeBytes_nil]⟩
  refine WP.sp_eq ?_
  refine wp_stb (a := P + BitVec.ofNat 64 k) (by decide) (by decide) (by rw [I.r3, BitVec.add_zero])
    (by rw [I.keep.2.2]; exact hw k hk) fun u₁ m₁ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun u₂ v₂ sp₂ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun u₃ v₃ sp₃ _ => WP.block_nil fun sp => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.r3, ptr_succ1]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.r5, count_sub hk]
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.r0]
  · refine ⟨fun r hr => ?_, by rw [v₃.rd, v₂.rd, m₁.rd, I.keep.2.1], by rw [v₃.wr, v₂.wr, m₁.wr, I.keep.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₃.other _ hr.2, v₂.other _ hr.1, m₁.gpr, I.keep.1 r (by simp [hr.1, hr.2])]
  · rw [sp, I.sp]
  · have h0 : (u.gpr .r0).setWidth 8 = 0 := by rw [I.r0]; rfl
    rw [v₃.mem, v₂.mem, m₁.mem, h0, I.mem, List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega),
      List.length_replicate]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.r5, count_sub hk]
    exact count_nz hk (by omega)

/-! ## The two exits -/

section
variable {G : GP} {X : State → Prop}

/-- No parameters: `out` zeroed, 0 returned. -/
theorem outZero_vp {g : Geo} {c : Cfg} {F : State → State → Prop} (hF : ∀ σ s, F σ s → St G c X σ s)
    (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) :
    VP F (seqs [.block [ld .r3 fOut, .li .r5 (2 * g.pLen + g.qLen)], zeroN, .block [.li .r3 0]])
      (fun σ t => FO G none σ t ∧ X σ) := by
  rw [hL, hQ]
  let M : State → State → Prop := fun σ t => St G c X σ t ∧ t.gpr .r3 = G.out ∧
    t.gpr .r5 = BitVec.ofNat 64 (2 * G.pLen + G.qLen)
  let P₃ : State → State → Prop := fun σ u => ∃ t, St G c X σ t ∧ Keep [.r0, .r3, .r5] t u ∧ u.sp = t.sp ∧
    Frame [G.rOut] t.mem u.mem ∧ Spec.Rsa.bytesAt u.mem G.out G.outLen = List.replicate G.outLen 0
  refine VP.seq (G := M) ?_ (VP.seq (G := P₃) ?_ ?_)
  · refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => (hF σ s h).1) []
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
        (.block [ld .r3 fOut, .li .r5 (2 * G.pLen + G.qLen)]), by kernel_rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
    obtain ⟨h, x⟩ := hF σ s hs
    have hE := h.gi.hEnd_le
    have n15 : 2 * G.pLen + G.qLen < 2 ^ 15 := by rcases h.gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    refine WP.cons (s' := s.write .r3 G.out) ?_ (WP.cons (s' := (s.write .r3 G.out).write .r5
      (BitVec.ofNat 64 (2 * G.pLen + G.qLen))) (exec_li n15) (WP.block_nil ?_))
    · rw [show ld .r3 fOut = .load .d .r3 .r28 fOut from rfl, exec_load_d (by decide) ⟨by decide, by decide⟩
        (by rw [h.gi.r28]; exact h.gi.inRdWr (by simp only [hEnd, fSave, fOut] at hE ⊢; omega)), h.gi.r28,
        show s.mem.readW (G.scr + BitVec.ofNat 64 fOut) 64 = G.out from h.gi.fixedV (by simp [fixedWords])]
    have k : BKeep [.r3, .r5] s ((s.write .r3 G.out).write .r5 (BitVec.ofNat 64 (2 * G.pLen + G.qLen))) :=
      (VG.Proof.Bignum.PPC64LE.Keep.write s .r3 _).trans (VG.Proof.Bignum.PPC64LE.Keep.write _ .r5 _)
    refine ⟨⟨h.of_keep ⟨k.gpr, k.rd, k.wr⟩ rfl k.sp, x⟩, ?_, (Upd.write _ _ _).gpr⟩
    rw [(Upd.write _ .r5 _).other .r3 (by decide), (Upd.write _ _ _).gpr]
  · refine VP.pub (G := G) (fun σ t h => ⟨h.1.1.gi.r28, by rw [h.1.1.gi.sp, ← h.1.1.gi.hG]; rfl⟩) [.r3, .r5]
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r3, .r5]) zeroN, by kernel_rfl⟩
      (fun σ₁ σ₂ s₁ s₂ ⟨_, a3, a5⟩ ⟨_, b3, b5⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a3, b3]
        · rw [a5, b5]) fun σ t ⟨⟨h, x⟩, t3, t5⟩ => ?_
    have gi := h.gi
    have hol := gi.outLen
    have fit := gi.outFit
    have hN : 0 < G.outLen := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    have o15 : G.outLen < 2 ^ 15 := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    refine WP.seq (WP.wr (exec_li (show 0 < 2 ^ 15 by decide)) fun t₁ u₁ sp₁ _ => WP.block_nil ?_)
    refine WP.mono (zeroLoop_ok (t := t₁) (P := G.out) (N := G.outLen) hN (by omega) fit
      (fun k hk => ⟨G.rOut, by rw [u₁.wr]; exact gi.outW, Offset.contains_base _ (by omega) (by omega)⟩)
      (by rw [u₁.other _ (by decide), t3]) (by rw [u₁.gpr]; rfl) (by rw [u₁.other _ (by decide), t5, hol]))
      fun u ⟨K, sp, m⟩ => ⟨t, ⟨h, x⟩, ?_, by rw [sp, sp₁], ?_, ?_⟩
    · refine ⟨fun r hr => ?_, by rw [K.2.1, u₁.rd], by rw [K.2.2, u₁.wr]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [K.1 r (by simp [hr.2.1, hr.2.2]), u₁.other _ hr.1]
    · rw [m, u₁.mem]; exact writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
    · rw [m, u₁.mem]
      have := bytesAt_writeBytes t.mem G.out (List.replicate G.outLen 0) (d := 0) (k := G.outLen)
        (by simp) (by simp; omega)
      rw [BitVec.add_zero] at this
      rw [this]; simp
  · refine VP.pub (G := G) (fun σ u ⟨t, ⟨h, _⟩, K, sp, _⟩ => ⟨(K.gpr (by decide)).trans h.gi.r28, by
        rw [sp, h.gi.sp, ← h.gi.hG]; rfl⟩) []
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [.li .r3 0]), by kernel_rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ u ⟨t, ⟨h, x⟩, K, sp, f, ho⟩ =>
      WP.wr (exec_li (show 0 < 2 ^ 15 by decide)) fun u' v sp' _ => WP.block_nil ⟨h.gi.fo (ws := [.r0, .r3, .r5] ++ [.r3])
        (K.trans ⟨fun r hr => v.other r (by simpa using hr), v.rd, v.wr⟩) (by rw [sp', sp])
        (by rw [v.mem]; exact f) (by rw [v.mem, ho]; rfl) (by rw [v.gpr]; rfl), x⟩

/-- Parameters at `sPacked`: copied to `out`, 1 returned. -/
theorem outCopy_vp {g : Geo} {c : Cfg} {a : Spec.Dsa.Params} {F : State → State → Prop}
    (hF : ∀ σ s, F σ s → St G c X σ s) (hcl : (sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a) ∈ c.cl)
    (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) :
    VP F (seqs [copyN [scr .r3 sPacked] [ld .r4 fOut] (2 * g.pLen + g.qLen), .block [.li .r3 1]])
      (fun σ t => FO G (some a) σ t ∧ X σ) := by
  rw [hL, hQ]
  have hlen := VG.Proof.Dsa.Generation.encodeParams_length G.pLen G.qLen a
  let M : State → State → Prop := fun σ t => St G c X σ t ∧ t.gpr .r3 = G.sa sPacked ∧ t.gpr .r4 = G.out ∧
    t.gpr .r5 = BitVec.ofNat 64 (2 * G.pLen + G.qLen)
  let P₃ : State → State → Prop := fun σ u => ∃ t, St G c X σ t ∧ Keep [.r3, .r4, .r5, .r6] t u ∧ u.sp = t.sp ∧
    Frame [G.rOut] t.mem u.mem ∧ Spec.Rsa.bytesAt u.mem G.out G.outLen = Spec.Dsa.encodeParams G.pLen G.qLen a
  refine VP.seq (G := P₃) (VP.seq (G := M) ?_ ?_) ?_
  · refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => (hF σ s h).1) []
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
        (.block ([scr .r3 sPacked] ++ [ld .r4 fOut] ++ [.li .r5 (2 * G.pLen + G.qLen)])), by kernel_rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
    obtain ⟨h, x⟩ := hF σ s hs
    have hE := h.gi.hEnd_le
    have n15 : 2 * G.pLen + G.qLen < 2 ^ 15 := by rcases h.gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    simp only [List.cons_append, List.nil_append]
    refine WP.cons (s' := s.write .r3 (G.sa sPacked)) ?_ (WP.cons (s' := (s.write .r3 (G.sa sPacked)).write .r4 G.out)
      ?_ (WP.cons (s' := ((s.write .r3 (G.sa sPacked)).write .r4 G.out).write .r5
        (BitVec.ofNat 64 (2 * G.pLen + G.qLen))) (exec_li n15) (WP.block_nil ?_)))
    · rw [show scr .r3 sPacked = .addi .r3 .r28 sPacked from rfl, exec_addi (by decide) (by decide), h.gi.r28]
    · have r28' : (s.write .r3 (G.sa sPacked)).gpr .r28 = G.scr := by
        rw [(Upd.write _ .r3 _).other .r28 (by decide), h.gi.r28]
      rw [show ld .r4 fOut = .load .d .r4 .r28 fOut from rfl, exec_load_d (by decide) ⟨by decide, by decide⟩
        (by rw [r28']; exact h.gi.inRdWr (by simp only [hEnd, fSave, fOut] at hE ⊢; omega)), r28']
      show some ((s.write .r3 (G.sa sPacked)).write .r4 (s.mem.readW (G.scr + BitVec.ofNat 64 fOut) 64)) = _
      rw [show s.mem.readW (G.scr + BitVec.ofNat 64 fOut) 64 = G.out from h.gi.fixedV (by simp [fixedWords])]
    have k : BKeep [.r3, .r4, .r5] s (((s.write .r3 (G.sa sPacked)).write .r4 G.out).write .r5
        (BitVec.ofNat 64 (2 * G.pLen + G.qLen))) :=
      ((VG.Proof.Bignum.PPC64LE.Keep.write s .r3 _).trans (VG.Proof.Bignum.PPC64LE.Keep.write _ .r4 _)).trans
        (VG.Proof.Bignum.PPC64LE.Keep.write _ .r5 _)
    refine ⟨⟨h.of_keep ⟨k.gpr, k.rd, k.wr⟩ rfl k.sp, x⟩, ?_, ?_, (Upd.write _ _ _).gpr⟩
    · rw [(Upd.write _ .r5 _).other .r3 (by decide), (Upd.write _ .r4 _).other .r3 (by decide), (Upd.write _ _ _).gpr]
    · rw [(Upd.write _ .r5 _).other .r4 (by decide), (Upd.write _ _ _).gpr]
  · refine VP.pub (G := G) (fun σ t h => ⟨h.1.1.gi.r28, by rw [h.1.1.gi.sp, ← h.1.1.gi.hG]; rfl⟩) [.r3, .r4, .r5]
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r3, .r4, .r5])
        (.loop (.block VG.Impl.MlKem.PPC64LE.copyBody) (.nonzero .d .r5)), by kernel_rfl⟩
      (fun σ₁ σ₂ s₁ s₂ ⟨_, a3, a4, a5⟩ ⟨_, b3, b4, b5⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [a3, b3]
        · rw [a4, b4]
        · rw [a5, b5]) fun σ t ⟨⟨h, x⟩, t3, t4, t5⟩ => ?_
    have gi := h.gi
    have hol := gi.outLen
    have big := gi.wBig
    have fit := gi.scrFit
    have ofit := gi.outFit
    have hN : 0 < G.outLen := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    have o15 : G.outLen < 2 ^ 15 := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    have hpk : sPacked + G.outLen ≤ G.scrLen * 8 := by
      have := (h.clOk _ hcl).2.2; simp only [hlen] at this; omega
    refine WP.mono (copyLoop_ok (S := G.sa sPacked) (D := G.out) (len := G.outLen) (by omega) hN
      (gi.out_scr.symm.sub_left (sw G hpk)) (fun i hi => by rw [GP.sa_add]; exact gi.inRdWr (by omega))
      (fun i hi => ⟨G.rOut, gi.outW, Offset.contains_base _ (by omega) (by omega)⟩) t3 t4 (by rw [t5, hol]))
      fun u ⟨K, sp, f, b⟩ => ⟨t, ⟨h, x⟩, K, sp, f, ?_⟩
    rw [b, hol, ← hlen]
    have e := h.sb _ hcl; dsimp only at e; exact e
  · refine VP.pub (G := G) (fun σ u ⟨t, ⟨h, _⟩, K, sp, _⟩ => ⟨(K.gpr (by decide)).trans h.gi.r28, by
        rw [sp, h.gi.sp, ← h.gi.hG]; rfl⟩) []
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [.li .r3 1]), by kernel_rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ u ⟨t, ⟨h, x⟩, K, sp, f, ho⟩ =>
      WP.wr (exec_li (show 1 < 2 ^ 15 by decide)) fun u' v sp' _ => WP.block_nil
        ⟨h.gi.fo (ws := [.r3, .r4, .r5, .r6] ++ [.r3])
        (K.trans ⟨fun r hr => v.other r (by simpa using hr), v.rd, v.wr⟩) (by rw [sp', sp])
        (by rw [v.mem]; exact f) (by rw [v.mem, ho]; rfl) (by rw [v.gpr]; rfl), x⟩

/-- The exit. -/
theorem finish_vp {g : Geo} (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) (R : Option Spec.Dsa.Params) :
    VP (St G (sFin G R) X) g.finish (fun σ t => FO G R σ t ∧ X σ) := by
  unfold Geo.finish
  cases R with
  | none =>
    refine VP.seq (G := fun σ s => St G (sFin G none) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [sFin])).trans (by simp [sFin]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    exact VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
      (outZero_vp (fun σ s h => h.1.1) hL hQ)
  | some a =>
    refine VP.seq (G := fun σ s => St G (sFin G (some a)) X σ s ∧ isa.eval (.zero .d .r0) s = some true)
      (cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [sFin])).trans (by simp [sFin]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    exact VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (outCopy_vp (fun σ s h => h.1.1) (by simp [sFin]) hL hQ)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)

end

end VG.Proof.Dsa.PPC64LE.Gen
