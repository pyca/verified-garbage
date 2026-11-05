module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.SLoop
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Entry
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Pre
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Frame
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter generation on PPC64LE: the exit

`finish_vp`: the result's words into the header (`dCfg`: the status, `used`,
`state[0]` and the next tape's length, computed for a tape that ran out by
`ranOut`), p‖q‖g copied from `sPacked` to `out` when the search found them,
else `out` zeroed (`OD`), then the words to `state` and `used` and the status
into `r3` (`FO`). `FO.restore`: then our caller's registers back.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.WriteBytes
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

/-- What `out` holds for the controller's end. -/
def outBytes (G : GP) (o : COut) : List Byte :=
  match o with
  | .found a _ => Spec.Dsa.encodeParams G.pLen G.qLen a
  | _ => List.replicate G.outLen 0

/-- After the exit: `out`, `used` and `state` hold the result, `r3` the status,
and the header our caller's registers. -/
structure FO (G : GP) (o : COut) (σ t : State) : Prop where
  pre : CIn 176 σ
  hG : mkG σ = G
  sp : t.sp = σ.sp
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  r28 : t.gpr .r28 = G.scr
  saved : ∀ i < 19, fw t.mem G (fSave + 8 * i) = σ.gpr (saved.getD i .r14)
  lr : fw t.mem G fLR = σ.lr
  frame : Frame [G.rOut, G.rUsed, G.rSt, G.rScr, rBelow σ 176] σ.mem t.mem
  out : Spec.Rsa.bytesAt t.mem G.out G.outLen = outBytes G o
  used : t.mem.readW (G.usedP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes G o).used
  st0 : t.mem.readW (G.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes G o).remaining
  st1 : t.mem.readW (G.stP + BitVec.ofNat 64 8) 64 = σ.mem.readW (G.stP + BitVec.ofNat 64 8) 64
  st2 : t.mem.readW (G.stP + BitVec.ofNat 64 16) 64 = σ.mem.readW (G.stP + BitVec.ofNat 64 16) 64
  st3 : t.mem.readW (G.stP + BitVec.ofNat 64 24) 64 =
    BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o))
  r3 : t.gpr .r3 = BitVec.ofNat 64 (cRes G o).status

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

/-- After the exit, `restore`. -/
theorem FO.restore {o : COut} {t : State} (h : FO G o σ t) :
    WP isa (.block restore) t fun u => abiPreserved σ u ∧ u.mem = t.mem ∧ u.gpr .r3 = t.gpr .r3 := by
  have big : 8 * (64 * G.pLen + 1024) ≤ G.scrLen * 8 := by
    have := h.pre.scrLen
    have e1 : pLenOf σ = G.pLen := by rw [← h.hG]; rfl
    have e2 : (σ.gpr .r9).toNat = G.scrLen := by rw [← h.hG]; rfl
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

/-! ## `out` -/

section
variable {G : GP} {X : State → Prop}

/-- `out` written with `ob`, from a stage `c` of the search at `t`. -/
def OD (G : GP) (c : Cfg) (X : State → Prop) (ob : List Byte) (σ u : State) : Prop :=
  ∃ t, St G c X σ t ∧ Keep [.r0, .r3, .r4, .r5, .r6] t u ∧ u.sp = t.sp ∧ Frame [G.rOut] t.mem u.mem ∧
    Spec.Rsa.bytesAt u.mem G.out G.outLen = ob

/-- No parameters: `out` zeroed. -/
theorem outZero_vp {g : Geo} {c : Cfg} {F : State → State → Prop} (hF : ∀ σ s, F σ s → St G c X σ s)
    (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) :
    VP F (seqs [.block [ld .r3 fOut, .li .r5 (2 * g.pLen + g.qLen)], zeroN])
      (OD G c X (List.replicate G.outLen 0)) := by
  rw [hL, hQ]
  let M : State → State → Prop := fun σ t => St G c X σ t ∧ t.gpr .r3 = G.out ∧
    t.gpr .r5 = BitVec.ofNat 64 (2 * G.pLen + G.qLen)
  refine VP.seq (G := M) ?_ ?_
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
      rw [K.1 r (by simp [hr.2.1, hr.2.2.2.1]), u₁.other _ hr.1]
    · rw [m, u₁.mem]; exact writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
    · rw [m, u₁.mem]
      have := bytesAt_writeBytes t.mem G.out (List.replicate G.outLen 0) (d := 0) (k := G.outLen)
        (by simp) (by simp; omega)
      rw [BitVec.add_zero] at this
      rw [this]; simp

/-- Parameters at `sPacked`: copied to `out`. -/
theorem outCopy_vp {g : Geo} {c : Cfg} {a : Spec.Dsa.Params} {F : State → State → Prop}
    (hF : ∀ σ s, F σ s → St G c X σ s) (hcl : (sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a) ∈ c.cl)
    (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) :
    VP F (copyN [scr .r3 sPacked] [ld .r4 fOut] (2 * g.pLen + g.qLen))
      (OD G c X (Spec.Dsa.encodeParams G.pLen G.qLen a)) := by
  rw [hL, hQ]
  have hlen := VG.Proof.Dsa.Generation.encodeParams_length G.pLen G.qLen a
  let M : State → State → Prop := fun σ t => St G c X σ t ∧ t.gpr .r3 = G.sa sPacked ∧ t.gpr .r4 = G.out ∧
    t.gpr .r5 = BitVec.ofNat 64 (2 * G.pLen + G.qLen)
  refine VP.seq (G := M) ?_ ?_
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
      fun u ⟨K, sp, f, b⟩ => ⟨t, ⟨h, x⟩, K.mono (by simp), sp, f, ?_⟩
    rw [b, hol, ← hlen]
    have e := h.sb _ hcl; dsimp only at e; exact e

/-! ## The result's words -/

/-- The result's words in the header. -/
abbrev dCfg (G : GP) (o : COut) : Cfg :=
  ((((cFin G o).setV fRU (BitVec.ofNat 64 (cRes G o).used)).setV fRet (BitVec.ofNat 64 (cRes G o).status)).setV fR0
    (BitVec.ofNat 64 (cRes G o).remaining)).setV fR3
      (BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)))

/-- A block of loads from and stores into the header and register operations. -/
theorem rb_vp {P Q : State → State → Prop} {c : Cfg} (hF : ∀ σ s, P σ s → St G c X σ s) {is : List Instr}
    (cert : ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28]) (.block is) hc).isSome = true)
    (wp : ∀ σ s, P σ s → SS G 176 σ c s → X σ → WP isa (.block is) s (Q σ)) : VP P (.block is) Q :=
  VP.pub (SS.pub (c := fun _ => c) fun σ s h => (hF σ s h).1) [] cert (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s h => wp σ s h (hF σ s h).1 (hF σ s h).2

/-- `budget v`: `r4 := 32769 v`. -/
theorem budget_ok {σ s : State} {c : Cfg} (h : SS G 176 σ c s) {v : Nat} (hv : v < 2 ^ 15) {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', SS G 176 σ c s' → Keep [.r4, .r5] s s' → s'.gpr .r4 = BitVec.ofNat 64 (32769 * v) →
      WP isa (.block rest) s' Q) : WP isa (.block (budget v ++ rest)) s Q := by
  refine h.wrK (exec_li hv) (by decide) fun s₁ h₁ u₁ => h₁.wrK (exec_lsl (by decide)) (by decide) fun s₂ h₂ u₂ =>
    h₂.wrK exec_add (by decide) fun s₃ h₃ u₃ => k s₃ h₃ ⟨fun r hr => ?_, by rw [u₃.rd, u₂.rd, u₁.rd],
      by rw [u₃.wr, u₂.wr, u₁.wr]⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₃.other _ hr.1, u₂.other _ hr.2, u₁.other _ hr.1]
  · rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega

/-- `results u v`: the result's words into the header, `used` from the header word `u`. -/
theorem results_vp {d : Cfg} {u : Nat} {U A B : BitVec 64} {v : Nat} (hv : v < 2 ^ 15) (hU : u ∈ d.LS)
    (hUv : d.V u = U) (hu : u + 8 ≤ hEnd) (hu8 : u % 8 = 0) {P : State → State → Prop}
    (hP : ∀ σ s, P σ s → St G d X σ s ∧ s.gpr .r5 = A ∧ s.gpr .r6 = B) :
    VP P (.block (Geo.results u v))
      (St G ((((d.setV fRU U).setV fRet (BitVec.ofNat 64 v)).setV fR0 A).setV fR3 B) X) := by
  refine rb_vp (fun σ s h => (hP σ s h).1) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block (Geo.results u v)), by kernel_rfl⟩ fun σ s hs h x => ?_
  obtain ⟨_, r5, r6⟩ := hP σ s hs
  refine h.ldK hu hu8 ((h.gi.slotV hU).trans hUv) (by decide) fun s₁ h₁ u₁ => ?_
  refine h₁.stF (o := fRU) (varOk_of (by decide)) fun s₂ h₂ m₂ _ => ?_
  rw [u₁.gpr] at h₂
  refine h₂.wrK (exec_li hv) (by decide) fun s₃ h₃ u₃ => ?_
  refine h₃.stF (o := fRet) (varOk_of (by decide)) fun s₄ h₄ m₄ _ => ?_
  rw [u₃.gpr] at h₄
  refine h₄.stF (o := fR0) (varOk_of (by decide)) fun s₅ h₅ m₅ _ => ?_
  rw [m₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), r5] at h₅
  refine h₅.stF (o := fR3) (varOk_of (by decide)) fun t ht _ _ => WP.block_nil ⟨?_, x⟩
  rw [m₅.gpr, m₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), r6] at ht
  exact ht

/-- `li r5, 0; li r6, 0; results u v`. -/
theorem zres_vp {d : Cfg} {u : Nat} {U : BitVec 64} {v : Nat} (hv : v < 2 ^ 15) (hU : u ∈ d.LS)
    (hUv : d.V u = U) (hu : u + 8 ≤ hEnd) (hu8 : u % 8 = 0) {P : State → State → Prop}
    (hP : ∀ σ s, P σ s → St G d X σ s) :
    VP P (.block (([.li .r5 0, .li .r6 0] : List Instr) ++ Geo.results u v))
      (St G ((((d.setV fRU U).setV fRet (BitVec.ofNat 64 v)).setV fR0 0).setV fR3 0) X) := by
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r5 = 0 ∧ s.gpr .r6 = 0)
    (rb_vp hP ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [.li .r5 0, .li .r6 0]),
      by kernel_rfl⟩ fun σ s hs h x => ?_) (results_vp hv hU hUv hu hu8 fun σ s h => h)
  refine h.wrK (exec_li (by decide)) (by decide) fun s₁ h₁ u₁ => h₁.wrK (exec_li (by decide)) (by decide)
    fun s₂ h₂ u₂ => WP.block_nil ⟨⟨h₂, x⟩, by rw [u₂.other _ (by decide), u₁.gpr]; rfl, by rw [u₂.gpr]; rfl⟩

theorem dCfg_ranOut (G : GP) (j c : Nat) :
    dCfg G (.ranOut j c) = if Spec.Dsa.parameterEntropy G.pLen ≤ G.witLen - c then
      (((((cFin G (.ranOut j c)).setV fRU (BitVec.ofNat 64 c)).setV fRet (BitVec.ofNat 64 3)).setV fR0 0).setV fR3 0)
    else (((((cFin G (.ranOut j c)).setV fRU (BitVec.ofNat 64 c)).setV fRet (BitVec.ofNat 64 0)).setV fR0
      (BitVec.ofNat 64 j)).setV fR3
        (BitVec.ofNat 64 (VG.Proof.Dsa.Generation.parameterRequest G.pLen (G.witLen - c)))) := by
  by_cases hb : Spec.Dsa.parameterEntropy G.pLen ≤ G.witLen - c <;>
    simp [dCfg, cRes, VG.Proof.Dsa.Generation.ranOutResult, hb, Spec.Entropy.Result.status,
      Spec.Entropy.Outcome.status, Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested,
      VG.Proof.Entropy.requested]

/-- `rand` ran out at the cursor `c` with `j` seeds left: the result's words. -/
theorem ranOut_vp {g : Geo} (hL : g.pLen = G.pLen) {j c : Nat} (hc : c ≤ G.witLen) (h64 : G.witLen < 2 ^ 64) :
    VP (St G (cFin G (.ranOut j c)) X) g.ranOut (St G (dCfg G (.ranOut j c)) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hp15 : G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  have hB : 32769 * G.pLen < 2 ^ 32 := by rcases l with e | e | e <;> rw [e] <;> decide
  generalize hd : cFin G (.ranOut j c) = d
  have hC : fC ∈ d.LS := by rw [← hd]; simp [cFin]
  have hCv : d.V fC = BitVec.ofNat 64 c := by rw [← hd]; simp [cFin, upd, fC, fSeedLeft, fStatus]
  have hS : fSeedLeft ∈ d.LS := by rw [← hd]; simp [cFin]
  have hSv : d.V fSeedLeft = BitVec.ofNat 64 j := by rw [← hd]; simp [cFin, upd, fSeedLeft, fStatus]
  rw [dCfg_ranOut, hd]
  unfold Geo.ranOut
  rw [hL]
  generalize ha : G.witLen - c = av
  have hav : av < 2 ^ 64 := by omega
  -- The octets left, against the budget.
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 av ∧
      s.gpr .r4 = BitVec.ofNat 64 (32769 * G.pLen) ∧
      isa.eval (.zero .d .r0) s = some (decide (av < 32769 * G.pLen)))
    (rb_vp (fun σ s h => h) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block ([ld .r3 fWitLen, ld .r4 fC, .sub .r3 .r3 .r4] ++ budget G.pLen ++ ltR)), by kernel_rfl⟩
      fun σ s _ h x => ?_) ?_
  · rw [List.append_assoc]
    simp only [List.cons_append, List.nil_append]
    refine h.ldK (o := fWitLen) (by decide) (by decide) (h.gi.fixedV (v := BitVec.ofNat 64 G.witLen)
      (by simp [fixedWords])) (by decide) fun s₁ h₁ u₁ => ?_
    refine h₁.ldK (o := fC) (by decide) (by decide) ((h₁.gi.slotV hC).trans hCv) (by decide) fun s₂ h₂ u₂ => ?_
    refine h₂.wrK exec_sub (by decide) fun s₃ h₃ u₃ => ?_
    have e3 : s₃.gpr .r3 = BitVec.ofNat 64 av := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, ← ha]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    refine budget_ok h₃ hp15 fun s₄ h₄ K₄ e₄ => ?_
    have e3' : s₄.gpr .r3 = BitVec.ofNat 64 av := by rw [K₄.gpr (by decide), e3]
    refine ltR_ok e3' e₄ fun t K m sp _ e => WP.block_nil ⟨⟨h₄.of_keep K m sp, x⟩, ?_, ?_, e.trans ?_⟩
    · rw [K.gpr (by decide), e3']
    · rw [K.gpr (by decide), e₄]
    · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt (by omega)]
  by_cases hb : Spec.Dsa.parameterEntropy G.pLen ≤ av
  · -- Exhausted.
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2.2.2, h₂.2.2.2])
      (VP.of_false fun σ s ⟨⟨_, _, _, e⟩, z⟩ => by
        rw [e] at z; simp only [Spec.Dsa.parameterEntropy] at hb; simp at z; omega)
      (zres_vp (by decide) hC hCv (by decide) (by decide) fun σ s h => h.1.1)
  rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
  simp only [Spec.Dsa.parameterEntropy, Nat.not_le] at hb
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2.2.2, h₂.2.2.2]) ?_
    (VP.of_false fun σ s ⟨⟨_, _, _, e⟩, z⟩ => by rw [e] at z; simp [hb] at z)
  -- At least `256 p_len`.
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 av ∧
      s.gpr .r4 = BitVec.ofNat 64 (G.pLen * 2 ^ 8) ∧
      isa.eval (.zero .d .r0) s = some (decide (av < G.pLen * 2 ^ 8)))
    (rb_vp (fun σ s h => h.1.1) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block (shl .r4 G.pLen 8 ++ ltR)), by kernel_rfl⟩ fun σ s ⟨⟨_, r3, _⟩, _⟩ h x => ?_) ?_
  · refine shl_ok h (r := .r4) (by decide) hp15 (by decide) fun s₁ h₁ K₁ e₁ _ => ?_
    have e3 : s₁.gpr .r3 = BitVec.ofNat 64 av := by rw [K₁.gpr (by decide), r3]
    refine ltR_ok e3 e₁ fun t K m sp _ e => WP.block_nil ⟨⟨h₁.of_keep K m sp, x⟩, ?_, ?_, e.trans ?_⟩
    · rw [K.gpr (by decide), e3]
    · rw [K.gpr (by decide), e₁]
    · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt (by omega)]
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 (max av (G.pLen * 2 ^ 8)))
    (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2.2.2, h₂.2.2.2])
      (rb_vp (fun σ s h => h.1.1) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
        (.block [.addi .r3 .r4 0]), by kernel_rfl⟩ fun σ s ⟨⟨_, _, r4, e⟩, z⟩ h x =>
          h.wrK (exec_addi (by decide) (by decide)) (by decide) fun t ht u => WP.block_nil ⟨⟨ht, x⟩, ?_⟩)
      (VP.block_nil fun σ s ⟨⟨h, r3, _, e⟩, z⟩ => ⟨h, ?_⟩)) ?_
  · have : av < G.pLen * 2 ^ 8 := by rw [e] at z; simpa using z
    rw [u.gpr, r4, BitVec.add_zero, Nat.max_eq_right (Nat.le_of_lt this)]
  · have : ¬av < G.pLen * 2 ^ 8 := by rw [e] at z; simpa using z
    rw [r3, Nat.max_eq_left (by omega)]
  -- Twice that, at most the budget.
  have hM : max av (G.pLen * 2 ^ 8) < 2 ^ 32 := by
    rcases l with e | e | e <;> rw [e] at hb ⊢ <;> omega
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 (2 * max av (G.pLen * 2 ^ 8)) ∧
      s.gpr .r4 = BitVec.ofNat 64 (32769 * G.pLen) ∧
      isa.eval (.zero .d .r0) s = some (decide (2 * max av (G.pLen * 2 ^ 8) < 32769 * G.pLen)))
    (rb_vp (fun σ s h => h.1) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block ([.add .r3 .r3 .r3] ++ budget G.pLen ++ ltR)), by kernel_rfl⟩ fun σ s ⟨_, r3⟩ h x => ?_) ?_
  · rw [List.append_assoc]
    simp only [List.cons_append, List.nil_append]
    refine h.wrK exec_add (by decide) fun s₁ h₁ u₁ => ?_
    have e1 : s₁.gpr .r3 = BitVec.ofNat 64 (2 * max av (G.pLen * 2 ^ 8)) := by
      rw [u₁.gpr, r3]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    refine budget_ok h₁ hp15 fun s₂ h₂ K₂ e₂ => ?_
    have e3 : s₂.gpr .r3 = BitVec.ofNat 64 (2 * max av (G.pLen * 2 ^ 8)) := by rw [K₂.gpr (by decide), e1]
    refine ltR_ok e3 e₂ fun t K m sp _ e => WP.block_nil ⟨⟨h₂.of_keep K m sp, x⟩, ?_, ?_, e.trans ?_⟩
    · rw [K.gpr (by decide), e3]
    · rw [K.gpr (by decide), e₂]
    · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hreq : VG.Proof.Dsa.Generation.parameterRequest G.pLen av =
      min (2 * max av (G.pLen * 2 ^ 8)) (32769 * G.pLen) := by
    simp only [VG.Proof.Dsa.Generation.parameterRequest, VG.Proof.Entropy.request, Spec.Dsa.parameterEntropy]
    rw [Nat.mul_comm G.pLen (2 ^ 8)]
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r3 =
      BitVec.ofNat 64 (VG.Proof.Dsa.Generation.parameterRequest G.pLen av))
    (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2.2.2, h₂.2.2.2])
      (VP.block_nil fun σ s ⟨⟨h, r3, _, e⟩, z⟩ => ⟨h, ?_⟩)
      (rb_vp (fun σ s h => h.1.1) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
        (.block [.addi .r3 .r4 0]), by kernel_rfl⟩ fun σ s ⟨⟨_, _, r4, e⟩, z⟩ h x =>
          h.wrK (exec_addi (by decide) (by decide)) (by decide) fun t ht u => WP.block_nil ⟨⟨ht, x⟩, ?_⟩)) ?_
  · have : 2 * max av (G.pLen * 2 ^ 8) < 32769 * G.pLen := by rw [e] at z; simpa using z
    rw [r3, hreq, Nat.min_eq_left (Nat.le_of_lt this)]
  · have : ¬2 * max av (G.pLen * 2 ^ 8) < 32769 * G.pLen := by rw [e] at z; simpa using z
    rw [u.gpr, r4, BitVec.add_zero, hreq, Nat.min_eq_right (by omega)]
  -- The words.
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r5 = BitVec.ofNat 64 j ∧
      s.gpr .r6 = BitVec.ofNat 64 (VG.Proof.Dsa.Generation.parameterRequest G.pLen av))
    (rb_vp (fun σ s h => h.1) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [.addi .r6 .r3 0, ld .r5 fSeedLeft]), by kernel_rfl⟩ fun σ s ⟨_, r3⟩ h x => ?_)
    (results_vp (by decide) hC hCv (by decide) (by decide) fun σ s h => h)
  refine h.wrK (exec_addi (by decide) (by decide)) (by decide) fun s₁ h₁ u₁ => ?_
  refine h₁.ldK (o := fSeedLeft) (by decide) (by decide) ((h₁.gi.slotV hS).trans hSv) (by decide)
    fun t ht u₂ => WP.block_nil ⟨⟨ht, x⟩, u₂.gpr, ?_⟩
  rw [u₂.other _ (by decide), u₁.gpr, r3, BitVec.add_zero]

/-! ## The words to `state` and `used` -/

/-- The words the write-back stores. -/
abbrev wbRegs (G : GP) : List Region :=
  [⟨G.stP + BitVec.ofNat 64 0, 8⟩, ⟨G.stP + BitVec.ofNat 64 24, 8⟩, ⟨G.usedP + BitVec.ofNat 64 0, 8⟩]

theorem readW_writeW_disj {m : Mem} {a b : Addr} {v : BitVec 64} (hd : Region.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  ((Frame.refl [⟨b, 8⟩] m).writeW List.mem_cons_self v (Region.contains_self _ _)).readW
    (Region.contains_self _ _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)

/-- A stage of the write-back: from `u₀`, where `out` is written, registers
changed and the words `wbRegs` written, with `P`. -/
def WBA (G : GP) (o : COut) (X : State → Prop) (P : State → Prop) (σ u : State) : Prop :=
  ∃ u₀, OD G (dCfg G o) X (outBytes G o) σ u₀ ∧ Keep [.r0, .r3, .r4, .r5, .r6] u₀ u ∧ u.sp = u₀.sp ∧
    Frame (wbRegs G) u₀.mem u.mem ∧ P u

/-- The facts a stage of the write-back rests on. -/
structure WBF (G : GP) (o : COut) (σ t u : State) : Prop where
  gi : SS G 176 σ (dCfg G o) t
  r28 : u.gpr .r28 = G.scr
  sp : u.sp = G.sp
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  hdr : ∀ o', o' + 8 ≤ hEnd → fw u.mem G o' = fw t.mem G o'

theorem wbf_of {o : COut} {σ t u₀ u : State} (ht : St G (dCfg G o) X σ t) (K : Keep [.r0, .r3, .r4, .r5, .r6] t u₀)
    (sp : u₀.sp = t.sp) (f : Frame [G.rOut] t.mem u₀.mem) (K' : Keep [.r0, .r3, .r4, .r5, .r6] u₀ u)
    (sp' : u.sp = u₀.sp) (f' : Frame (wbRegs G) u₀.mem u.mem) : WBF G o σ t u := by
  have gi := ht.1.gi
  have pre := gi.pre
  have hE := gi.hEnd_le
  have fit := gi.scrFit
  refine ⟨ht.1, (K'.gpr (by decide)).trans ((K.gpr (by decide)).trans gi.r28),
    by rw [sp', sp, gi.sp, ← gi.hG]; rfl, by rw [K'.2.1, K.2.1], by rw [K'.2.2, K.2.2], fun o' ho' => ?_⟩
  have hs : Region.Sub (G.rs o' 8) G.rScr := sw G (by omega)
  have cS := pre.cS; have uC := pre.uC; have oC := pre.oC; rw [gi.hG] at cS uC oC
  rw [fw_frame f' (fun r hr => ?_), fw_frame f (fun r hr => ?_)]
  · simp only [List.mem_singleton] at hr; subst hr
    exact oC.symm.sub_left hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (cS.sub_left hs).sub_right (Offset.sub_base (d := 0) (n := 8) (k := 32) G.stP (by decide))
    · exact (cS.sub_left hs).sub_right (Offset.sub_base (d := 24) (n := 8) (k := 32) G.stP (by decide))
    · exact (uC.symm.sub_left hs).sub_right (Offset.sub_base (d := 0) (n := 8) (k := 8) G.usedP (by decide))

theorem WBA.facts {o : COut} {P : State → Prop} {σ u : State} (h : WBA G o X P σ u) :
    ∃ t, WBF G o σ t u ∧ X σ := by
  obtain ⟨u₀, ⟨t, ht, K, sp, f, _⟩, K', sp', f', _⟩ := h
  exact ⟨t, wbf_of ht K sp f K' sp' f', ht.2⟩

/-- A load of a header word in the write-back. -/
theorem WBA.ldH {o : COut} {P : State → Prop} {σ u : State} (h : WBA G o X P σ u) {o' : Nat} (ho : o' + 8 ≤ hEnd)
    (h8 : o' % 8 = 0) {v : BitVec 64} (hv : ∀ t, SS G 176 σ (dCfg G o) t → fw t.mem G o' = v) {r : Reg}
    {rest : List Instr} {Q : State → Prop} (k : ∀ u', Upd u u' r v → u'.sp = u.sp → WP isa (.block rest) u' Q) :
    WP isa (.block (ld r o' :: rest)) u Q := by
  obtain ⟨t, F, _⟩ := h.facts
  have hE := F.gi.gi.hEnd_le
  have e : u.mem.readW (G.sa o') 64 = v := (F.hdr o' ho).trans (hv t F.gi)
  refine WP.cons (s' := u.write r v) ?_ (k _ (Upd.write _ _ _) rfl)
  rw [show ld r o' = .load .d r .r28 o' from rfl, exec_load_d (by decide)
    ⟨by simp only [hEnd, fSave] at ho; omega, by omega⟩ (by rw [F.r28, F.rd, F.wr]; exact F.gi.gi.inRdWr (by omega)),
    F.r28, e]

theorem WBA.pub {o : COut} {P : State → Prop} : Pub G (WBA G o X P) := fun σ u h => by
  obtain ⟨t, F, _⟩ := h.facts; exact ⟨F.r28, F.sp⟩

/-- A step of the write-back that keeps what was written. -/
theorem WBA.step {o : COut} {P P' : State → Prop} {σ u u' : State} (h : WBA G o X P σ u) {ws : List Reg}
    (K : Keep ws u u') (hws : ∀ r ∈ ws, r ∈ [Reg.r0, .r3, .r4, .r5, .r6]) (sp : u'.sp = u.sp)
    (f : Frame (wbRegs G) u.mem u'.mem) (p : P' u') : WBA G o X P' σ u' := by
  obtain ⟨u₀, hod, K₀, sp₀, f₀, _⟩ := h
  exact ⟨u₀, hod, K₀.trans (K.mono hws) |>.mono (by simp), by rw [sp, sp₀], f₀.trans f, p⟩

theorem WBA.upd {o : COut} {P P' : State → Prop} {σ u u' : State} (h : WBA G o X P σ u) {r : Reg} {v : BitVec 64}
    (up : Upd u u' r v) (hr : r ∈ [Reg.r0, .r3, .r4, .r5, .r6]) (sp : u'.sp = u.sp) (p : P' u') : WBA G o X P' σ u' :=
  h.step (ws := [r]) ⟨fun r' hr' => up.other r' (by simpa using hr'), up.rd, up.wr⟩ (by simpa using hr) sp
    (by rw [up.mem]; exact Frame.refl _ _) p

/-- What the write-back's stages rest on: where the words are. -/
structure WBW (G : GP) (σ : State) : Prop where
  inS0 : InRegions σ.wr (G.stP + BitVec.ofNat 64 0) 8
  inS3 : InRegions σ.wr (G.stP + BitVec.ofNat 64 24) 8
  inU : InRegions σ.wr (G.usedP + BitVec.ofNat 64 0) 8
  d03 : Region.Disjoint ⟨G.stP + BitVec.ofNat 64 0, 8⟩ ⟨G.stP + BitVec.ofNat 64 24, 8⟩
  d0U : Region.Disjoint ⟨G.stP + BitVec.ofNat 64 0, 8⟩ ⟨G.usedP + BitVec.ofNat 64 0, 8⟩
  d3U : Region.Disjoint ⟨G.stP + BitVec.ofNat 64 24, 8⟩ ⟨G.usedP + BitVec.ofNat 64 0, 8⟩

theorem wbw_of {σ t : State} {c : Cfg} (h : SS G 176 σ c t) : WBW G σ := by
  have pre := h.gi.pre
  have nS := pre.nS; have nU := pre.nU
  have uS := pre.uS; rw [h.gi.hG] at uS
  have eS : (σ.gpr .r10).toNat = G.stP.toNat := by rw [← h.gi.hG]; rfl
  have eU : (σ.gpr .r5).toNat = G.usedP.toNat := by rw [← h.gi.hG]; rfl
  have w : σ.wr = [G.rOut, G.rUsed, G.rScr, G.rSt] := by rw [pre.wr, h.gi.hG]
  refine ⟨⟨G.rSt, by rw [w]; simp, Offset.contains_base _ (show 0 + 8 ≤ 32 by decide) (by decide)⟩,
    ⟨G.rSt, by rw [w]; simp, Offset.contains_base _ (show 24 + 8 ≤ 32 by decide) (by decide)⟩,
    ⟨G.rUsed, by rw [w]; simp, Offset.contains_base _ (show 0 + 8 ≤ 8 by decide) (by decide)⟩,
    Offset.disjoint _ (by decide) (by omega) (by omega), ?_, ?_⟩
  · exact (uS.symm.sub_left (Offset.sub_base (d := 0) (n := 8) (k := 32) _ (by decide))).sub_right
      (Offset.sub_base (d := 0) (n := 8) (k := 8) _ (by decide))
  · exact (uS.symm.sub_left (Offset.sub_base (d := 24) (n := 8) (k := 32) _ (by decide))).sub_right
      (Offset.sub_base (d := 0) (n := 8) (k := 8) _ (by decide))

theorem WBA.wbw {o : COut} {P : State → Prop} {σ u : State} (h : WBA G o X P σ u) : WBW G σ ∧ u.wr = σ.wr := by
  obtain ⟨t, F, _⟩ := h.facts
  exact ⟨wbw_of F.gi, by rw [F.wr, F.gi.gi.wr]⟩

/-- A store of `r4` through `r3` into one of the words. -/
theorem WBA.st {o : COut} {P P' : State → Prop} {σ u : State} (h : WBA G o X P σ u) {a : Addr} {off : Nat}
    (ha : u.gpr .r3 + BitVec.ofNat 64 off = a) (ho : off < 2 ^ 15 ∧ off % 4 = 0) (hin : InRegions σ.wr a 8)
    (hr : ⟨a, 8⟩ ∈ wbRegs G) {rest : List Instr} {Q : State → State → Prop}
    (p : ∀ u', u'.gpr = u.gpr → u'.mem = u.mem.writeW a (u.gpr .r4) → P' u')
    (k : ∀ u', WBA G o X P' σ u' → WP isa (.block rest) u' (Q σ)) :
    WP isa (.block (.store .d .r4 .r3 off :: rest)) u (Q σ) :=
  wp_std' (by decide) ho ha (by rw [h.wbw.2]; exact hin) fun u' m sp _ =>
    k u' (h.step (ws := []) ⟨fun r _ => by rw [m.gpr], m.rd, m.wr⟩ (by simp) sp
      (by rw [m.mem]; exact (Frame.refl _ _).writeW hr _ (Region.contains_self _ _)) (p u' m.gpr m.mem))

theorem WBA.p {o : COut} {P : State → Prop} {σ u : State} (h : WBA G o X P σ u) : P u := by
  obtain ⟨_, _, _, _, _, p⟩ := h; exact p

/-- The words of `state` the search keeps. -/
theorem keepWord {o : COut} {P : State → Prop} {σ u : State} (h : WBA G o X P σ u) {d : Nat}
    (hd : d = 8 ∨ d = 16) : u.mem.readW (G.stP + BitVec.ofNat 64 d) 64 = σ.mem.readW (G.stP + BitVec.ofNat 64 d) 64 := by
  obtain ⟨u₀, ⟨t, ⟨ht, _⟩, _, _, f, _⟩, _, _, f', _⟩ := h
  have gi := ht.gi
  have pre := gi.pre
  have nS := pre.nS; have nU := pre.nU
  have eS : (σ.gpr .r10).toNat = G.stP.toNat := by rw [← gi.hG]; rfl
  have uS := pre.uS; have oS := pre.oS; have cS := pre.cS; have bS := pre.bS
  rw [gi.hG] at uS oS cS bS
  have sub : Region.Sub ⟨G.stP + BitVec.ofNat 64 d, 8⟩ G.rSt := Offset.sub_base (k := 32) _ (by omega)
  rw [f'.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide),
    f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide),
    gi.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cS.symm.sub_left sub
    · exact bS.symm.sub_left sub
  · simp only [List.mem_singleton] at hr; subst hr
    exact oS.symm.sub_left sub
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (uS.symm.sub_left sub).sub_right (Offset.sub_base (d := 0) (n := 8) (k := 8) _ (by decide))

/-- The last stage of the write-back: `FO`. -/
theorem fo_of {o : COut} {σ u : State}
    (h : WBA G o X (fun u => u.mem.readW (G.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes G o).remaining ∧
      u.mem.readW (G.stP + BitVec.ofNat 64 24) 64 =
        BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)) ∧
      u.mem.readW (G.usedP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes G o).used) σ u)
    (r3 : u.gpr .r3 = BitVec.ofNat 64 (cRes G o).status) : FO G o σ u ∧ X σ := by
  have k8 := keepWord h (d := 8) (.inl rfl)
  have k16 := keepWord h (d := 16) (.inr rfl)
  obtain ⟨u₀, ⟨t, ⟨ht, x⟩, K, sp, f, ob⟩, K', sp', f', p0, p3, pU⟩ := h
  have F := wbf_of ⟨ht, x⟩ K sp f K' sp' f'
  have gi := ht.gi
  have pre := gi.pre
  have big := gi.wBig
  have fit := gi.scrFit
  have hE := gi.hEnd_le
  have nS := pre.nS; have nU := pre.nU
  have eS : (σ.gpr .r10).toNat = G.stP.toNat := by rw [← gi.hG]; rfl
  have eU : (σ.gpr .r5).toNat = G.usedP.toNat := by rw [← gi.hG]; rfl
  have uS := pre.uS; have oS := pre.oS; have oU := pre.oU; have nO := pre.nO
  rw [gi.hG] at uS oS oU
  have eO : (σ.gpr .r3).toNat + (σ.gpr .r4).toNat = G.out.toNat + G.outLen := by rw [← gi.hG]; rfl
  have hfr : Frame [G.rOut, G.rUsed, G.rSt, G.rScr, rBelow σ 176] σ.mem u.mem := by
    refine (gi.frame.mono fun r hr => ?_).trans ((f.mono fun r hr => ?_).trans (f'.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
    · simp only [List.mem_singleton] at hr; subst hr; simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨G.rSt, by simp, Offset.sub_base (k := 32) _ (by decide)⟩
      · exact ⟨G.rSt, by simp, Offset.sub_base (k := 32) _ (by decide)⟩
      · exact ⟨G.rUsed, by simp, Offset.sub_base (k := 8) _ (by decide)⟩
  refine ⟨⟨pre, gi.hG, F.sp.trans (by rw [← gi.hG]; rfl), by rw [F.rd, gi.rd], by rw [F.wr, gi.wr], F.r28,
    fun i hi => by rw [F.hdr _ (by simp only [hEnd]; omega)]; exact gi.saved i hi,
    by rw [F.hdr _ (by decide)]; exact gi.lr, hfr, ?_, pU, p0, k8, k16, p3, r3⟩, x⟩
  rw [VG.Proof.Dsa.Generation.frame_bytesAt f' (fun r hr => ?_) (by omega)]
  · exact ob
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact oS.sub_right (Offset.sub_base (k := 32) _ (by decide))
    · exact oS.sub_right (Offset.sub_base (k := 32) _ (by decide))
    · exact oU.sub_right (Offset.sub_base (k := 8) _ (by decide))

/-- The words to `state` and `used`, and the status into `r3`. -/
theorem writeBack_vp (o : COut) :
    VP (OD G (dCfg G o) X (outBytes G o)) (.block Geo.writeBack) (fun σ t => FO G o σ t ∧ X σ) := by
  refine (show VP (WBA G o X (fun _ => True)) _ _ from ?_).mono
    (fun σ u h => ⟨u, h, Keep.refl _ _, rfl, Frame.refl _ _, trivial⟩) (fun _ _ h => h)
  rw [show Geo.writeBack = [ld .r3 fStP, ld .r4 fR0] ++ ([.store .d .r4 .r3 0] ++ ([ld .r4 fR3] ++
    ([.store .d .r4 .r3 24] ++ ([ld .r3 fUsedP, ld .r4 fRU] ++ ([.store .d .r4 .r3 0] ++ [ld .r3 fRet]))))) from rfl]
  have vR0 : ∀ σ t, SS G 176 σ (dCfg G o) t → fw t.mem G fR0 = BitVec.ofNat 64 (cRes G o).remaining :=
    fun σ t h => (h.gi.slotV (by simp)).trans (by simp [upd, fR0, fR3])
  have vR3 : ∀ σ t, SS G 176 σ (dCfg G o) t → fw t.mem G fR3 =
      BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)) :=
    fun σ t h => (h.gi.slotV (by simp)).trans (by simp [upd])
  have vRU : ∀ σ t, SS G 176 σ (dCfg G o) t → fw t.mem G fRU = BitVec.ofNat 64 (cRes G o).used :=
    fun σ t h => (h.gi.slotV (by simp)).trans (by simp [upd, fR0, fR3, fRet, fRU])
  have vRet : ∀ σ t, SS G 176 σ (dCfg G o) t → fw t.mem G fRet = BitVec.ofNat 64 (cRes G o).status :=
    fun σ t h => (h.gi.slotV (by simp)).trans (by simp [upd, fR0, fR3, fRet])
  have vSt : ∀ σ t, SS G 176 σ (dCfg G o) t → fw t.mem G fStP = G.stP :=
    fun σ t h => h.gi.fixedV (by simp [fixedWords])
  have vUs : ∀ σ t, SS G 176 σ (dCfg G o) t → fw t.mem G fUsedP = G.usedP :=
    fun σ t h => h.gi.fixedV (by simp [fixedWords])
  -- `r3` := `state`, `r4` := `state[0]`.
  refine VP.block_append (G := WBA G o X fun u => u.gpr .r3 = G.stP ∧
      u.gpr .r4 = BitVec.ofNat 64 (cRes G o).remaining)
    (VP.pub WBA.pub [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [ld .r3 fStP, ld .r4 fR0]), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
      fun σ u h => h.ldH (by decide) (by decide) (vSt σ) fun u₁ up₁ sp₁ => ?_) ?_
  · have h₁ : WBA G o X (fun u' => u'.gpr .r3 = G.stP) σ u₁ := h.upd up₁ (by simp) sp₁ up₁.gpr
    exact h₁.ldH (by decide) (by decide) (vR0 σ) fun u₂ up₂ sp₂ =>
      WP.block_nil (h₁.upd up₂ (by simp) sp₂ ⟨by rw [up₂.other _ (by decide), up₁.gpr], up₂.gpr⟩)
  -- `state[0]`.
  refine VP.block_append (G := WBA G o X fun u => u.gpr .r3 = G.stP ∧
      u.mem.readW (G.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes G o).remaining)
    (VP.pub WBA.pub [.r3] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r3])
      (.block [.store .d .r4 .r3 0]), by kernel_rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.p.1, h₂.p.1])
      fun σ u h => h.st (by rw [h.p.1]) ⟨by decide, by decide⟩ h.wbw.1.inS0 (by simp)
        (fun u' g m => ⟨by rw [g]; exact h.p.1, by rw [m, Mem.readW_writeW_self64, h.p.2]⟩)
        fun u' h' => WP.block_nil h') ?_
  -- `r4` := `state[3]`.
  refine VP.block_append (G := WBA G o X fun u => u.gpr .r3 = G.stP ∧
      u.gpr .r4 = BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)) ∧
      u.mem.readW (G.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes G o).remaining)
    (VP.pub WBA.pub [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [ld .r4 fR3]), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
      fun σ u h => h.ldH (by decide) (by decide) (vR3 σ) fun u₁ up₁ sp₁ => WP.block_nil
        (h.upd up₁ (by simp) sp₁ ⟨by rw [up₁.other _ (by decide)]; exact h.p.1, up₁.gpr,
          by rw [up₁.mem]; exact h.p.2⟩)) ?_
  -- `state[3]`.
  refine VP.block_append (G := WBA G o X fun u =>
      u.mem.readW (G.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes G o).remaining ∧
      u.mem.readW (G.stP + BitVec.ofNat 64 24) 64 =
        BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)))
    (VP.pub WBA.pub [.r3] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r3])
      (.block [.store .d .r4 .r3 24]), by kernel_rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.p.1, h₂.p.1])
      fun σ u h => h.st (by rw [h.p.1]) ⟨by decide, by decide⟩ h.wbw.1.inS3 (by simp)
        (fun u' _ m => ⟨by rw [m, readW_writeW_disj h.wbw.1.d03, h.p.2.2],
          by rw [m, Mem.readW_writeW_self64, h.p.2.1]⟩)
        fun u' h' => WP.block_nil h') ?_
  -- `r3` := `used`, `r4` := its word.
  refine VP.block_append (G := WBA G o X fun u => u.gpr .r3 = G.usedP ∧
      u.gpr .r4 = BitVec.ofNat 64 (cRes G o).used ∧
      u.mem.readW (G.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes G o).remaining ∧
      u.mem.readW (G.stP + BitVec.ofNat 64 24) 64 =
        BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)))
    (VP.pub WBA.pub [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [ld .r3 fUsedP, ld .r4 fRU]), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
      fun σ u h => h.ldH (by decide) (by decide) (vUs σ) fun u₁ up₁ sp₁ => ?_) ?_
  · have h₁ : WBA G o X (fun u' => u'.gpr .r3 = G.usedP ∧
        u'.mem.readW (G.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes G o).remaining ∧
        u'.mem.readW (G.stP + BitVec.ofNat 64 24) 64 =
          BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o))) σ u₁ :=
      h.upd up₁ (by simp) sp₁ ⟨up₁.gpr, by rw [up₁.mem]; exact h.p.1, by rw [up₁.mem]; exact h.p.2⟩
    exact h₁.ldH (by decide) (by decide) (vRU σ) fun u₂ up₂ sp₂ =>
      WP.block_nil (h₁.upd up₂ (by simp) sp₂ ⟨by rw [up₂.other _ (by decide)]; exact h₁.p.1, up₂.gpr,
        by rw [up₂.mem]; exact h₁.p.2.1, by rw [up₂.mem]; exact h₁.p.2.2⟩)
  -- `used`.
  refine VP.block_append (G := WBA G o X fun u =>
      u.mem.readW (G.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes G o).remaining ∧
      u.mem.readW (G.stP + BitVec.ofNat 64 24) 64 =
        BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)) ∧
      u.mem.readW (G.usedP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes G o).used)
    (VP.pub WBA.pub [.r3] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r3])
      (.block [.store .d .r4 .r3 0]), by kernel_rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.p.1, h₂.p.1])
      fun σ u h => h.st (by rw [h.p.1]) ⟨by decide, by decide⟩ h.wbw.1.inU (by simp)
        (fun u' _ m => ⟨by rw [m, readW_writeW_disj h.wbw.1.d0U, h.p.2.2.1],
          by rw [m, readW_writeW_disj h.wbw.1.d3U, h.p.2.2.2], by rw [m, Mem.readW_writeW_self64, h.p.2.1]⟩)
        fun u' h' => WP.block_nil h') ?_
  -- The status.
  exact VP.pub WBA.pub [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
      (.block [ld .r3 fRet]), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
      fun σ u h => h.ldH (by decide) (by decide) (vRet σ) fun u₁ up₁ sp₁ => WP.block_nil
        (fo_of (h.upd up₁ (by simp) sp₁ ⟨by rw [up₁.mem]; exact h.p.1, by rw [up₁.mem]; exact h.p.2.1,
          by rw [up₁.mem]; exact h.p.2.2⟩) up₁.gpr)

theorem dCfg_found (G : GP) (a : Spec.Dsa.Params) (u : Nat) :
    dCfg G (.found a u) = ((((cFin G (.found a u)).setV fRU (BitVec.ofNat 64 u)).setV fRet (BitVec.ofNat 64 1)).setV
      fR0 0).setV fR3 0 := by
  simp [dCfg, cRes, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status,
    Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested, VG.Proof.Entropy.requested]

theorem dCfg_noSeeds (G : GP) (c : Nat) :
    dCfg G (.noSeeds c) = ((((cFin G (.noSeeds c)).setV fRU (BitVec.ofNat 64 c)).setV fRet (BitVec.ofNat 64 3)).setV
      fR0 0).setV fR3 0 := by
  simp [dCfg, cRes, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status,
    Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested, VG.Proof.Entropy.requested]

/-- The exit. -/
theorem finish_vp {g : Geo} (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) (o : COut) (hok : cOk G o)
    (h64 : G.witLen < 2 ^ 64) :
    VP (St G (cFin G o) X) g.finish (fun σ t => FO G o σ t ∧ X σ) := by
  unfold Geo.finish
  have hc : ∀ {F : State → State → Prop} {b : Bool}, (∀ σ s, F σ s → isa.eval (.zero .d .r0) s = some b) →
      ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval (.zero .d .r0) s₁ = isa.eval (.zero .d .r0) s₂ :=
    fun hF _ _ _ _ h₁ h₂ => by rw [hF _ _ h₁, hF _ _ h₂]
  have no : ∀ {F : State → State → Prop} {c : Prog isa} {Q : State → State → Prop} {b : Bool},
      VP (fun σ s => (F σ s ∧ isa.eval (.zero .d .r0) s = some b) ∧ isa.eval (.zero .d .r0) s = some (!b)) c Q := by
    intro F c Q b
    exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; cases b <;> simp at z
  cases o with
  | found a u =>
    refine VP.seq (G := fun σ s => St G (cFin G (.found a u)) X σ s ∧ isa.eval (.zero .d .r0) s = some true)
      (cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [cFin])).trans (by simp [cFin]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.seq (G := St G (dCfg G (.found a u)) X) (VP.ite (hc fun σ s h => h.2)
      ((zres_vp (u := fUsed) (U := BitVec.ofNat 64 u) (by decide) (by simp [cFin]) (by simp [cFin, upd, fUsed, fStatus])
        (by decide) (by decide) fun σ s h => h.1.1).mono (fun _ _ h => h) fun σ s h => by
          rw [dCfg_found]; exact h) no) ?_
    refine VP.seq (G := fun σ s => St G (dCfg G (.found a u)) X σ s ∧ isa.eval (.zero .d .r0) s = some true)
      (cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [cFin])).trans (by simp [cFin, upd, fStatus, fR3, fR0, fRet, fRU]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    exact VP.seq (VP.ite (hc fun σ s h => h.2)
      (outCopy_vp (fun σ s h => h.1.1) (by simp [cFin]) hL hQ) no) (writeBack_vp _)
  | noSeeds c =>
    refine VP.seq (G := fun σ s => St G (cFin G (.noSeeds c)) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 3) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [cFin])).trans (by simp [cFin]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.seq (G := St G (dCfg G (.noSeeds c)) X) (VP.ite (hc fun σ s h => h.2) no ?_) ?_
    · refine VP.seq (G := fun σ s => St G (cFin G (.noSeeds c)) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
        (cmpF_vp (x := BitVec.ofNat 64 3) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.1.1.gi.slotV (by simp [cFin])).trans (by simp [cFin]))
          fun σ s t ⟨⟨⟨_, x⟩, _⟩, _⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
      exact VP.ite (hc fun σ s h => h.2) no
        ((zres_vp (u := fC) (U := BitVec.ofNat 64 c) (by decide) (by simp [cFin]) (by simp [cFin, upd, fC, fStatus])
          (by decide) (by decide) fun σ s h => h.1.1).mono (fun _ _ h => h) fun σ s h => by
            rw [dCfg_noSeeds]; exact h)
    refine VP.seq (G := fun σ s => St G (dCfg G (.noSeeds c)) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 3) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [cFin])).trans (by simp [cFin, upd, fStatus, fR3, fR0, fRet, fRU]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    exact VP.seq (VP.ite (hc fun σ s h => h.2) no (outZero_vp (fun σ s h => h.1.1) hL hQ)) (writeBack_vp _)
  | ranOut j c =>
    refine VP.seq (G := fun σ s => St G (cFin G (.ranOut j c)) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [cFin])).trans (by simp [cFin]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.seq (G := St G (dCfg G (.ranOut j c)) X) (VP.ite (hc fun σ s h => h.2) no ?_) ?_
    · refine VP.seq (G := fun σ s => St G (cFin G (.ranOut j c)) X σ s ∧ isa.eval (.zero .d .r0) s = some true)
        (cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.1.1.gi.slotV (by simp [cFin])).trans (by simp [cFin]))
          fun σ s t ⟨⟨⟨_, x⟩, _⟩, _⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
      exact VP.ite (hc fun σ s h => h.2) ((ranOut_vp hL hok.1 h64).mono (fun σ s h => h.1.1) fun _ _ h => h) no
    refine VP.seq (G := fun σ s => St G (dCfg G (.ranOut j c)) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [cFin])).trans (by simp [cFin, upd, fStatus, fR3, fR0, fRet, fRU]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    exact VP.seq (VP.ite (hc fun σ s h => h.2) no (outZero_vp (fun σ s h => h.1.1) hL hQ)) (writeBack_vp _)

end

end VG.Proof.Dsa.PPC64LE.Gen
