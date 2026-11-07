module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.Fn
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTOpen
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTOne
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTVerify
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.Fn
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTOpen
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTOne
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTVerify
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-!
# AES-GCM decryption out of place, RISC-V: constant time

Untrusted: everything here is checked by Lean. As `vg_aes_gcm_open`'s
(`CTOpen.lean`), whose body's proof (`openGood_ct`) serves both: the entry,
then `tag_len` (`s8`), public, and the two branches of `tagLenOk`; once the
tag length is allowed, the data is decrypted only if the tags are equal,
which may differ between two runs only as the result does (the contract's
`pub`). At the end the destination is zeroed only if the result is 0: the
addresses `wipe` computes from the slots of `W` are the destination's in
both runs (`wipeArgs_ok`), and its loop is on them.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)

theorem openToRes_isSome {t : State} (hok : Spec.Gcm.tagLenOk (stackArg t 3).toNat = true) :
    (openToRes t).isSome = decide (OpenTagOk t (stackArg t 2) (stackArg t 3).toNat) := by
  have e : openToRes t = if OpenTagOk t (stackArg t 2) (stackArg t 3).toNat then
      some (Spec.Gcm.gctr (Spec.Gcm.ctxCiph t.mem (t.gpr .a0) (t.gpr .a1).toNat)
        (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH t.mem (t.gpr .a0)) (bytesAt t.mem (t.gpr .a2) (t.gpr .a3).toNat)))
        (bytesAt t.mem (t.gpr .a6) (t.gpr .a7).toNat)) else none := by
    simp only [openToRes, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  rw [e]
  by_cases h : OpenTagOk t (stackArg t 2) (stackArg t 3).toNat
  · simp only [eq_true h, ite_true, decide_true, Option.isSome_some]
  · simp only [eq_false h, ite_false, decide_false, Option.isSome_none]

theorem openToHead_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block [.addSp .t1 0, .load .d .t1 .t1 32]) h).isSome = true := ⟨_, by taint_decide⟩

theorem openToRest_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1])
    (.block (oneRestAt 16 ++ ([.load .d .s8 .t1 24, .load .d .t2 .t1 0, .sub .t2 .t2 .a6,
      .store .d .t2 .s0 dstO] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem wipeArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s0, .s11])
    (.block [.load .d .t2 .s0 dataO, .load .d .t3 .s0 dstO, .add .t2 .t2 .t3, mov .t3 .s11, .li .t1 0]) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem wipeLoop_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.t2, .t3])
    (.ite (.zero .t3) (.block [])
      (.loop (.block [.store .b .t1 .t2 0, .addi .t2 .t2 1, .addi .t3 .t3 (-1)]) (.nonzero .t3))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem a0Zero_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block ([] : List Instr)) h).isSome = true := ⟨_, by taint_decide⟩

/-- The head of `vg_aes_gcm_open_to`'s entry: `W`, at `sp + 32`, into `t1`. -/
theorem oneA32_ok {s₀ : State} {W : Addr} (hsa : s₀.sp.toNat % 16 = 0)
    (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 32) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 32) 64 = W) :
    WP isa (.block [.addSp .t1 0, .load .d .t1 .t1 32]) s₀ fun sA =>
      sA.gpr .t1 = W ∧ (∀ r, r ≠ .t1 → sA.gpr r = s₀.gpr r) ∧ Keeps s₀ sA := by
  refine Steps.wp_addSp (imm := 0) (by decide) fun sA uA => ?_
  refine Steps.wp_ld (off := 32) (a := s₀.sp + BitVec.ofNat 64 32) (by decide) (by rw [uA.gpr, add_ofNat_zero])
    (Spill.al8 (by omega) (by decide)) (by rw [uA.rd, uA.wr]; exact hWi) fun sB uB => WP.block_nil ?_
  exact ⟨by rw [uB.gpr, uA.mem, hWv], fun r hr => by rw [uB.other r hr, uA.other r hr],
    ⟨by rw [uB.mem, uA.mem], by rw [uB.rd, uA.rd], by rw [uB.wr, uA.wr], by rw [uB.sp, uA.sp]⟩⟩

/-- After the entry (and `s5` restored), what the pieces need. -/
theorem openTo_one {t₀ s : State} (h : openToPreR t₀)
    (h1 : SO2 true (stackArg t₀ 4) (stackArg t₀ 2) (stackArg t₀ 0) t₀ s) (h19 : s.gpr .s8 = stackArg t₀ 3) :
    OneO true (t₀.gpr .a0) (stackArg t₀ 4) t₀.sp (t₀.gpr .a1).toNat (t₀.gpr .a2) (t₀.gpr .a3).toNat (t₀.gpr .a4)
        (t₀.gpr .a5) (t₀.gpr .a6) (t₀.gpr .a7) (stackArg t₀ 2) (stackArg t₀ 3) (stackArg t₀ 0) s ∧
      s.gpr .s4 = t₀.gpr .a2 ∧ s.gpr .s5 = BitVec.ofNat 64 (t₀.gpr .a3).toNat := by
  have hp := h.opre
  have hk₀ := hp.stk
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hN : DataOk (stackArg t₀ 4 + BitVec.ofNat 64 16) (stackArg t₀ 4) s (t₀.gpr .a2) (t₀.gpr .a3).toNat :=
    ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.nonce, (t₀.gpr .a3).isLt, hp.fn, hp.dnW.sub_right (Lay.wSub (by decide)),
      hp.dnW, by rw [hk₁.sp]; exact hp.bufs _ (by simp)⟩
  have hA : DataOk (stackArg t₀ 4 + BitVec.ofNat 64 16) (stackArg t₀ 4) s (t₀.gpr .a4) (t₀.gpr .a5).toNat :=
    ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.aad, (t₀.gpr .a5).isLt, hp.fa, hp.daW.sub_right (Lay.wSub (by decide)),
      hp.daW, by rw [hk₁.sp]; exact hp.bufs _ (by simp)⟩
  have hT : Covers [⟨stackArg t₀ 2, (stackArg t₀ 3).toNat⟩] (s.rd ++ s.wr) := by
    rw [hk₁.rd, hk₁.wr]; exact hp.tag
  exact ⟨⟨⟨s.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3]; exact toN, by rw [h1.s7]; exact toN, h1.s10, h1.s11,
    h1.env hp.ctx hp.w hk₀, hN, hA, hp.dsrc.of_eq hk₁.rd hk₁.wr hk₁.sp, h1.aad, h1.dat⟩, h1.s9, h19, hT,
    ⟨hp.ddst.of_eq hk₁.rd hk₁.wr hk₁.sp, hp.alias⟩, h1.dst⟩, h1.s4, by rw [h1.s5]; exact toN⟩

/-- `mv s5, s7` after `tagLenOk`: the entry's registers again. -/
theorem mov25_so2 {W T Dst : Addr} {t₀ s₂ s₃ s₄ : State} (h2 : SO2 true W T Dst t₀ s₂)
    (g : ∀ r, r ≠ .t0 → r ≠ .s5 → s₃.gpr r = s₂.gpr r) (k : Keeps s₂ s₃) (u : Steps.Upd s₃ s₄ .s5 (s₃.gpr .s7)) :
    SO2 true W T Dst t₀ s₄ ∧ s₄.gpr .s8 = s₂.gpr .s8 := by
  refine ⟨h2.keep (fun r h0 _ => ?_) ⟨by rw [u.mem, k.mem], by rw [u.rd, k.rd], by rw [u.wr, k.wr],
    by rw [u.sp, k.sp]⟩, by rw [u.other _ (by decide), g _ (by decide) (by decide)]⟩
  by_cases e : r = .s5
  · subst e
    rw [u.gpr, g _ (by decide) (by decide), h2.s7, h2.s5]
  · rw [u.other r e, g r h0 e]

theorem openTo_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa openToRISCV64.pre openToRISCV64.pub OpenTo.openTo := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩, qres⟩ := hq
  have h₁' : openToPreR σ₁ := h₁
  have hp₁ := h₁'.opre
  have hR := hp₁.rounds
  let I₀ : State → Prop := fun s => openToPreR s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ stackArg s 2 = stackArg σ₁ 2 ∧ stackArg s 3 = stackArg σ₁ 3 ∧
    stackArg s 4 = stackArg σ₁ 4 ∧ (openToRes s).isSome = (openToRes σ₁).isSome
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm,
    q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm,
    (qa 1 (by decide)).symm, (qa 2 (by decide)).symm, (qa 3 (by decide)).symm, (qa 4 (by decide)).symm,
    (qres hR).symm⟩, ?_⟩
  unfold OpenTo.openTo openWith
  -- the entry: its head loads `W` from a public address, the rest saves through it
  let J₁ : State → Prop := fun s => ∃ t₀, I₀ t₀ ∧ SO2 true (stackArg t₀ 4) (stackArg t₀ 2) (stackArg t₀ 0) t₀ s ∧
    s.gpr .s8 = stackArg t₀ 3
  refine CT.seq (J := J₁) ?_ (fun s hs => WP.mono (openToEntry_wp hs.1) fun s' ⟨a, b⟩ => ⟨s, hs, a, b⟩) ?_
  · let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 4 else σ₁.gpr r
    have hl : openEntryWith true = [.addSp .t1 0, .load .d .t1 .t1 32] ++ (oneRestAt 16 ++
        ([.load .d .s8 .t1 24, .load .d .t2 .t1 0, .sub .t2 .t2 .a6, .store .d .t2 .s0 dstO] : List Instr)) := by
      simp only [openEntryWith, ↓reduceIte, oneEntryAt_eq, List.append_assoc]
    rw [hl]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := openToHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, _, _, _, ea4, _⟩
      have hsa : s.sp.toNat % 16 = 0 := hs.opre.al
      obtain ⟨hrd, -⟩ := id hs
      have hA : Covers [args s 5] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
      have hin : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 32) 8 := by
        have := in_off hA (d := 32) (n := 8) (by decide) (by decide)
        rwa [stackArgAddr_0, add_ofNat_assoc, Nat.zero_add] at this
      refine WP.mono (oneA32_ok (W := stackArg s 4) hsa hin rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea4, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := openToRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  -- the tag length
  let ok := Spec.Gcm.tagLenOk (stackArg σ₁ 3).toNat
  let J₂ : State → Prop := fun s => ∃ t₀ s₂, I₀ t₀ ∧ SO2 true (stackArg t₀ 4) (stackArg t₀ 2) (stackArg t₀ 0) t₀ s₂ ∧
    s₂.gpr .s8 = stackArg t₀ 3 ∧ (∀ r, r ≠ .t0 → r ≠ .s5 → s.gpr r = s₂.gpr r) ∧ Keeps s₂ s ∧
    s.gpr .s5 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J₂) ?_ (fun s ⟨t₀, ht, h1, h19⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint'
    exact CT.taintEq _ (fun _ => stackArg σ₁ 3) σ₁.sp (fun s ⟨t₀, ht, h1, h19⟩ =>
      ⟨h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1, by simp [h19, ht.2.2.2.2.2.2.2.2.2.2.2.2.2.1]⟩) hc
  · have h19' : s.gpr .s8 = BitVec.ofNat 64 (stackArg t₀ 3).toNat := by rw [h19]; simp
    refine WP.mono (tagLenOk_ok h19' (stackArg t₀ 3).isLt) fun s' ⟨h25, g, k⟩ =>
      ⟨t₀, s, ht, h1, h19, g, k, ?_⟩
    rw [h25, ht.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  -- the two branches
  have ev : ∀ s, J₂ s → isa.eval (.zero .s5) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, _, _, _, _, h25⟩ => eval_zero h25 (by split <;> decide)
  have L₀ := hp₁.lay
  let res := (openToRes σ₁).isSome
  let J₃ : State → Prop := fun s => s.gpr .s0 = stackArg σ₁ 4 ∧ s.sp = σ₁.sp ∧ s.gpr .s11 = σ₁.gpr .a7 ∧
    s.gpr .a0 = BitVec.ofNat 64 (if res then 1 else 0) ∧
    s.mem.readW (stackArg σ₁ 4 + BitVec.ofNat 64 dataO) 64 = σ₁.gpr .a6 ∧
    s.mem.readW (stackArg σ₁ 4 + BitVec.ofNat 64 dstO) 64 = stackArg σ₁ 0 - σ₁.gpr .a6 ∧
    Covers [⟨stackArg σ₁ 4, 2560⟩] (s.rd ++ s.wr) ∧ Covers [⟨stackArg σ₁ 0, (σ₁.gpr .a7).toNat⟩] s.wr
  refine CT.seq (J := J₃) (CT.ite _ ev (fun _ => ?_) (fun hb => ?_)) (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [.li .a0 0] (.inl rfl)
    exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
      ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
  · have hok : ok = true := by
      cases e : ok
      · simp [e] at hb
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    refine CT.seq ?_ (fun s ⟨t₀, s₂, ht, h1, h19, g, k, _⟩ => ?_)
      (openGood_ct (sp := σ₁.sp) (Np := σ₁.gpr .a2) (n := (σ₁.gpr .a3).toNat) (Ad := σ₁.gpr .a4) (A := σ₁.gpr .a5)
        (D := σ₁.gpr .a6) (Ln := σ₁.gpr .a7) (o := true) (Dst := stackArg σ₁ 0) L₀ hR
        (hp₁.dtW.sub_right (Lay.wSub (by decide))) t1 t16 res)
    · obtain ⟨_, hc⟩ := nil_taint [mov .s5 .s7] (.inr (.inl rfl))
      exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
        ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
    · obtain ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, ea3, ea4, eres⟩ := ht
      refine Steps.wp_mv fun s₄ u => WP.block_nil ?_
      obtain ⟨h4, h19₄⟩ := mov25_so2 h1 g k u
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 3).toNat = true := by rw [ea3]; exact hok
      have o := openTo_one hpre h4 (h19₄.trans h19)
      rw [e3, e4, e5, e6, e7, e8, e9, e10, ea0, ea2, ea3, ea4, esp] at o
      refine ⟨o, open_head hpre.opre h4 (by rw [h19₄.trans h19]; simp) hok₀ (T' := .block [])
        fun s₉ om => WP.block_nil_iff.mpr ?_⟩
      show s₉.gpr .s8 = _
      rw [om.s8]
      show _ = BitVec.ofNat 64 (if (openToRes σ₁).isSome = true then 1 else 0)
      rw [← eres, openToRes_isSome hok₀]
      by_cases hx : OpenTagOk t₀ (stackArg t₀ 2) (stackArg t₀ 3).toNat
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  · -- what both branches leave: the result, which both runs agree on, and the slots `wipe` reads
    obtain ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, ea3, ea4, eres⟩, h1, h19, g, k, h25⟩ := hs
    have hp := hpre.opre
    have hW₀ : Covers [⟨stackArg σ₁ 4, 2560⟩] (t₀.rd ++ t₀.wr) := by rw [← ea4]; exact Covers.right hp.w
    have hD₀ : Covers [⟨stackArg σ₁ 0, (σ₁.gpr .a7).toNat⟩] t₀.wr := by rw [← ea0, ← e10]; exact hp.dst
    refine WP.ite _ (ev s ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, ea3, ea4, eres⟩, h1, h19,
      g, k, h25⟩) (fun ht => ?_) (fun hf => ?_)
    · have hbad : ok = false := by
        cases e : ok
        · rfl
        · simp [e] at ht
      have hres : res = false := by
        show (openToRes σ₁).isSome = false
        simp only [openToRes, Spec.Gcm.openResult]
        rw [show Spec.Gcm.tagLenOk (stackArg σ₁ 3).toNat = false from hbad]
        rfl
      refine Steps.wp_li (imm := 0) (by decide) fun s' u => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [u.other _ (by decide), g _ (by decide) (by decide), h1.s0, ea4]
      · rw [u.sp, k.sp, h1.keeps.sp, esp]
      · rw [u.other _ (by decide), g _ (by decide) (by decide), h1.s11, e10]
      · rw [u.gpr, hres]; rfl
      · rw [u.mem, k.mem, ← ea4, h1.dat, e9]
      · rw [u.mem, k.mem, ← ea4, h1.dst rfl, ea0, e9]
      · rw [u.rd, u.wr, k.rd, k.wr, h1.keeps.rd, h1.keeps.wr]; exact hW₀
      · rw [u.wr, k.wr, h1.keeps.wr]; exact hD₀
    · have hok : ok = true := by
        cases e : ok
        · simp [e] at hf
        · rfl
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 3).toNat = true := by rw [ea3]; exact hok
      refine WP.seq (Steps.wp_mv fun s₄ u => WP.block_nil ?_)
      obtain ⟨h4, h19₄⟩ := mov25_so2 h1 g k u
      refine WP.mono (open_good hp h4 (by rw [h19₄.trans h19]; simp) hok₀) fun s' bo =>
        ⟨by rw [bo.s0, ea4], by rw [bo.sp, esp], by rw [bo.s11, e10], ?_, by rw [← ea4, bo.dat, e9],
          by rw [← ea4, bo.dst rfl, ea0, e9], by rw [bo.rd, bo.wr]; exact hW₀, by rw [bo.wr]; exact hD₀⟩
      show _ = BitVec.ofNat 64 (if (openToRes σ₁).isSome then 1 else 0)
      rw [bo.a0, ← eres, openToRes_isSome hok₀]
      by_cases hx : OpenTagOk t₀ (stackArg t₀ 2) (stackArg t₀ 3).toNat
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  -- the end: the destination zeroed if the result is 0, then `restore`
  have ev₀ : ∀ s, J₃ s → isa.eval (.zero .a0) s = some (decide ((if res then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, h3, _⟩ => eval_zero h3 (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .s0 = stackArg σ₁ 4 ∧ s.sp = σ₁.sp)
    (CT.ite _ ev₀ (fun _ => ?_) (fun _ => CT.skip)) (fun s hs => ?_) ?_
  · -- `wipe`: its first block, then its loop on the destination
    let J₄ : State → Prop := fun s => s.sp = σ₁.sp ∧ s.gpr .s0 = stackArg σ₁ 4 ∧ s.gpr .t2 = stackArg σ₁ 0 ∧
      s.gpr .t3 = BitVec.ofNat 64 (σ₁.gpr .a7).toNat
    unfold wipe
    refine CT.seq (J := J₄) ?_ (fun s ⟨h31, hsp, h23, _, hS, hδ, hW, _⟩ => WP.mono
      (wipeArgs_ok h31 hp₁.wa hW hS hδ (n := (σ₁.gpr .a7).toNat) (by rw [h23]; simp))
      fun s' ⟨t2, t3, _, g', k'⟩ => ⟨k'.sp.trans hsp, by rw [g' _ (by decide) (by decide) (by decide), h31], t2, t3⟩) ?_
    · obtain ⟨_, hc⟩ := wipeArgs_taint
      exact CT.taintEq _ (fun r => if r = .s0 then stackArg σ₁ 4 else σ₁.gpr .a7) σ₁.sp
        (fun s ⟨h31, hsp, h23, _⟩ => ⟨hsp, by simp [h31, h23]⟩) hc
    · obtain ⟨_, hc⟩ := wipeLoop_taint
      exact CT.taintEq _ (fun r => if r = .t2 then stackArg σ₁ 0 else BitVec.ofNat 64 (σ₁.gpr .a7).toNat) σ₁.sp
        (fun s ⟨hsp, _, h2, h3⟩ => ⟨hsp, by simp [h2, h3]⟩) hc
  · obtain ⟨h31, hsp, h23, h3, hS, hδ, hW, hdw⟩ := hs
    refine WP.ite _ (ev₀ s ⟨h31, hsp, h23, h3, hS, hδ, hW, hdw⟩) (fun _ => ?_) (fun _ => WP.block_nil ⟨h31, hsp⟩)
    have fD : (stackArg σ₁ 0).toNat + (σ₁.gpr .a7).toNat ≤ 2 ^ 64 := hp₁.fD
    exact WP.mono (wipe_ok h31 hp₁.wa hW hS hδ (n := (σ₁.gpr .a7).toNat) (by rw [h23]; simp) (σ₁.gpr .a7).isLt
      fD hdw) fun u ⟨_, _, gu, _, _, spu⟩ => ⟨by rw [gu _ (by decide) (by decide) (by decide)]; exact h31,
        spu.trans hsp⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq _ (fun _ => stackArg σ₁ 4) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64
