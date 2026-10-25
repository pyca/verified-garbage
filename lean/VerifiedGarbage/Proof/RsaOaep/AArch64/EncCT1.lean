module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCTBase
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEm
import VerifiedGarbage.Proof.RsaOaep.AArch64.Args
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCTBase
meta import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
meta import VerifiedGarbage.Proof.Mgf1.Basic
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEm
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Args
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSAES-OAEP encryption on AArch64: `EM` and the call in constant time

`encMain` from two runs in the same layout (`encMain_tr`): the copies into
`EM` from the registers their heads fix (`*E_pin`), the label's hash and
MGF1 as for any caller (`pw_lr`), the arguments' blocks by the taint
analysis, and the call of a precomputed public operation, whose public
arguments, `pre`'s words and `e` agree in both runs (`pdCallCT`). Nothing
after the call branches on its result.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked pdCallCT)

/-- Two layouts' `pre` from the two entry memories are the same. -/
theorem pre_eq {L : ELay} {m₁ m₂ : Mem} (q₁ : PreOk L m₁) (q₂ : PreOk L m₂) :
    preW L m₁ = preW L m₂ ∧ prlW L m₁ = prlW L m₂ := by
  have h := q₁.hx.symm.trans q₂.hx
  simp only [List.cons.injEq, Region.mk.injEq, and_true] at h
  exact ⟨h.1, BitVec.eq_of_toNat_eq (by omega)⟩

/-- The registers of the call, with the first run's `pre`. -/
theorem readyP_of {L : ELay} {m m' : Mem} {t : State} (q : PreOk L m) (q' : PreOk L m') (h : PReadyP L m t) :
    PReadyP L m' t := by
  obtain ⟨w, wl⟩ := pre_eq q q'
  exact ⟨h.x0, h.x1, h.x2.trans w, h.x3.trans wl, h.x4, h.x5, h.x6, h.x7⟩

theorem putMsg_eq : putMsg = .seq (.block ((([.ldrSp .x11 sMsg] : List Instr) ++ scr .x12 oEm ++
    ([.ldrSp .x10 sK, .add .x .x12 .x12 .x10, .ldrSp .x13 sMsgLen, .sub .x .x12 .x12 .x13,
      .subImm .x .x12 .x12 1] : List Instr)) ++
    ([.movz .x .x10 1 0, .strb .x10 .x12 0, .addImm .x .x12 .x12 1] : List Instr)))
    (.ite (.nonzero .x .x13) copyLoop (.block [])) := rfl

variable {Hl Gm : Hash} (hH : StreamOK Hl.stream) (hG : StreamOK Gm.stream)

include hH hG in
theorem encMain_tr {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D) (hGv : Proof.Mgf1.Valid Gs) (c : PdChecked)
    {P : Nat} {e : Env} (hL : e.L.Ok) (hP : c.stack ≤ e.L.P) (hP16 : 16 ≤ e.L.P) (hD : e.L.D = Hl.D)
    (q₁ : PreOk e.L e.m₁) (q₂ : PreOk e.L e.m₂) (hk : 2 * Hl.D + 2 + e.L.ml.toNat ≤ e.L.k.toNat) :
    RelCT isa (PW P e fun _ _ => True) (Impl.RsaOaep.AArch64.Precomputed.encMain Hl Gm c.name c.code)
      fun _ _ => True := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  replace hD0 : 0 < Hl.D := hD0
  have hk1024 := hL.k1024
  have cSt : oSt = 3072 := rfl
  have cR : oRsa = 8192 := rfl
  have f4 : MFit 1 Hl.D (1 + Hl.D) (e.L.k.toNat - Hl.D - 1) :=
    ⟨by rw [cSt]; omega_arith, by rw [cSt]; omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  have f2 : MFit (1 + Hl.D) (e.L.k.toNat - Hl.D - 1) 1 Hl.D :=
    ⟨by rw [cSt]; omega_arith, by rw [cSt]; omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  have ly : ∀ {g vv m₀} {t : State} {V W}, Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W → Slots e.L W →
      Lay t e.L.Q e.L.scr := fun hc R hS => hc.lay hL hP16 R hS.scr
  have hk3 : ∀ {W : Nat → BitVec 64}, Slots e.L W → W 21 = BitVec.ofNat 64 e.L.k.toNat := fun hS => by
    rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm3 : ∀ {W : Nat → BitVec 64}, Slots e.L W → W 28 = BitVec.ofNat 64 e.L.ml.toNat := fun hS => by
    rw [hS.ml, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- The seed's and the message's bytes are apart from our working space.
  have hsdS : ∀ i < Hl.D, ∀ j < oRsa, off e.L.sd i ≠ off e.L.scr j := fun i hi j hj
      (h' : e.L.sd + BitVec.ofNat 64 i = e.L.scr + BitVec.ofNat 64 j) =>
    (hL.sR _ (ro_SD e.L)) _ (hL.ours_scr _ (Offset.contains_base e.L.scr (d := j) (n := 1) (by omega_arith) (by omega_arith)))
      (h' ▸ Offset.contains_base e.L.sd (d := i) (n := 1) (k := e.L.D) (by omega_arith)
        (by have := hL.bR _ (ro_SD e.L); simp only at this; omega_arith))
  have hmsS : ∀ i < e.L.ml.toNat, ∀ j < oRsa, off e.L.msg i ≠ off e.L.scr j := fun i hi j hj
      (h' : e.L.msg + BitVec.ofNat 64 i = e.L.scr + BitVec.ofNat 64 j) =>
    (hL.sR _ (ro_MSG e.L)) _ (hL.ours_scr _ (Offset.contains_base e.L.scr (d := j) (n := 1) (by omega_arith) (by omega_arith)))
      (h' ▸ Offset.contains_base e.L.msg (d := i) (n := 1) (k := e.L.ml.toNat) (by omega_arith)
        (by have := hL.bR _ (ro_MSG e.L); simp only at this; omega_arith))
  have inRd : ∀ {g vv m₀} {u : State} {R : Region}, Ctx e.L g vv m₀ u →
      R ∈ [e.L.N, e.L.E, e.L.LAB, e.L.MSG, e.L.SD] ++ e.L.X ++ [e.L.ARGS] →
      ∀ {a : Addr} {n : Nat}, R.Contains a n → InRegions (u.rd ++ u.wr) a n := fun hcu hR _ _ h3 =>
    ⟨_, List.mem_append_left _ (by rw [hcu.rd]; exact hR), h3⟩
  simp only [Impl.RsaOaep.AArch64.Precomputed.encMain, encEm, seqs]
  -- `EM`'s place cleared.
  refine RelCT.seq (R := PW P e fun _ _ => True) (RelCT.seq (pw_wp (X' := fun _ _ => True) (pw_seq_tr [.x11, .x12, .x13]
      (fun r => ([(Reg.x11, off e.L.scr oEm), (.x12, BitVec.ofNat 64 128), (.x13, BitVec.ofNat 64 0)].lookup r).getD 0)
      (by taint_decide) (by taint_decide) fun _ _ _ _ _ _ _ _ hc R hS _ => clearE_pin (ly hc R hS))
    fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (clearEm_ok (ly hc R hS) R)
      fun _ ⟨_, Su, Ru⟩ => In.of_step hL hP16 hc Su nil_ws Ru hS trivial) ?_) ?_
  -- The seed.
  · refine RelCT.seq (pw_wp (X' := fun _ _ => True) (pw_seq_tr [.x11, .x12, .x13]
        (fun r => ([(Reg.x11, e.L.sd), (.x12, off e.L.scr (oEm + 1)), (.x13, BitVec.ofNat 64 Hl.D)].lookup r).getD 0)
        (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (([.ldrSp .x11 sSeed] : List Instr) ++
          scr .x12 (oEm + 1) ++ ([.movz .x .x13 (BitVec.ofNat 16 gH.D) 0] : List Instr))) (by rfl) (by taint_decide))
        (by taint_decide) fun _ _ _ _ _ _ _ _ hc R hS _ => seedE_pin (ly hc R hS) R hS.sd hD64)
      fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (copySeed_ok (ly hc R hS) R (H := Hl) hS.sd hD0 hD64
        (fun i hi => inRd hc (by simp) (Offset.contains_base e.L.sd (d := i) (n := 1) (k := e.L.D) (by omega_arith)
          (by have := hL.bR _ (ro_SD e.L); simp only at this; omega_arith)))
        (fun i hi j hj => hsdS i hi _ (by unfold oEm; omega_arith)))
        fun _ ⟨_, Su, Ru⟩ => In.of_step hL hP16 hc Su nil_ws Ru hS trivial) ?_
    -- The label's hash.
    refine RelCT.seq (pw_wp (X' := fun _ _ => True)
      (pw_lr hP16 (hashLabel_tr hH e.L.labl.isLt (.inl rfl)
        (X := fun W t => LabAt t e.L.Q e.L.scr W e.L.lab e.L.labl.toNat) fun _ _ h => h)
        fun _ _ _ _ _ _ hc hS _ => hc.labAt hL hP16 hS)
      fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (hashLabel_ok hH (Hs := Hs) hHh (ly hc R hS) R
        (hc.labAt hL hP16 hS) (o := oDig) (.inl rfl))
        fun _ ⟨_, Su, _, Ru, _, _⟩ => In.of_step hL hP16 hc Su nil_ws Ru hS trivial) ?_
    -- `lHash` after the seed.
    refine RelCT.seq (pw_wp (X' := fun _ _ => True) (pw_seq_tr [.x11, .x12, .x13]
        (fun r => ([(Reg.x11, off e.L.scr oDig), (.x12, off e.L.scr (oEm + 1 + Hl.D)),
          (.x13, BitVec.ofNat 64 Hl.D)].lookup r).getD 0)
        (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (scr .x11 oDig ++ scr .x12 (oEm + 1 + gH.D) ++
          ([.movz .x .x13 (BitVec.ofNat 16 gH.D) 0] : List Instr))) (by rfl) (by taint_decide))
        (by taint_decide) fun _ _ _ _ _ _ _ _ hc R hS _ => lhE_pin (ly hc R hS) hD64)
      fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (copyLh_ok (ly hc R hS) R (H := Hl) hD0 hD64)
        fun _ ⟨_, Su, Ru⟩ => In.of_step hL hP16 hc Su nil_ws Ru hS trivial) ?_
    -- `0x01` and the message.
    refine pw_wp (X' := fun _ _ => True) (by
        rw [putMsg_eq]
        exact RelCT.seq_block_append (pw_seq_tr [.x11, .x12, .x13]
          (fun r => ([(Reg.x11, e.L.msg), (.x12, off e.L.scr (e.L.k.toNat - e.L.ml.toNat - 1)),
            (.x13, BitVec.ofNat 64 e.L.ml.toNat)].lookup r).getD 0)
          (by taint_decide) (by taint_decide)
          fun _ _ _ _ _ _ _ _ hc R hS _ => msgE_pin (ly hc R hS) R (hk3 hS) (hm3 hS) hS.msg (by omega_arith)))
      fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (putMsg_ok (ly hc R hS) R (hk3 hS) (hm3 hS) hS.msg (by omega_arith)
        hk1024 (fun i hi => inRd hc (by simp) (Offset.contains_base e.L.msg (d := i) (n := 1) (k := e.L.ml.toNat)
          (by omega_arith) (by have := hL.bR _ (ro_MSG e.L); simp only at this; omega_arith))) hmsS)
        fun _ ⟨_, Su, Ru⟩ => In.of_step hL hP16 hc Su nil_ws Ru hS trivial
  -- `DB` masked.
  refine RelCT.seq (pw_blk (X' := fun W _ => MArgs W e.L.scr 1 Hl.D (1 + Hl.D) (e.L.k.toNat - Hl.D - 1)) []
    (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (dbArgs gH)) (by rfl) (by taint_decide)) nopin
    fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (dbArgs_ok (ly hc R hS) R (hk3 hS) (by omega_arith) (by omega_arith) hk1024 [])
      fun _ ⟨_, Su, Ru⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega_arith)) (mW_args _ _ _ _ _ _)) ?_
  refine RelCT.seq (pw_wp (X' := fun _ _ => True) (pw_lr hP16 (mgfXor_tr hG f4 fun _ _ h => h)
      fun _ _ _ _ _ _ _ _ x => x)
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (mgfXor_ok hG hGh hGl hGv (ly hc R hS) R f4 hx)
      fun _ ⟨_, Su, _, W', Ru, hW', _⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ h2 h3 => hW' j (by unfold nW frameBytes; omega_arith) (by omega_arith) (by omega_arith)) trivial) ?_
  -- The seed masked.
  refine RelCT.seq (pw_blk (X' := fun W _ => MArgs W e.L.scr (1 + Hl.D) (e.L.k.toNat - Hl.D - 1) 1 Hl.D) []
    (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (seedArgs gH)) (by rfl) (by taint_decide)) nopin
    fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (seedArgs_ok (ly hc R hS) R (hk3 hS) (by omega_arith) (by omega_arith) hk1024 [])
      fun _ ⟨_, Su, Ru⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega_arith)) (mW_args _ _ _ _ _ _)) ?_
  refine RelCT.seq (pw_wp (X' := fun _ _ => True) (pw_lr hP16 (mgfXor_tr hG f2 fun _ _ h => h)
      fun _ _ _ _ _ _ _ _ x => x)
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (mgfXor_ok hG hGh hGl hGv (ly hc R hS) R f2 hx)
      fun _ ⟨_, Su, _, W', Ru, hW', _⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ h2 h3 => hW' j (by unfold nW frameBytes; omega_arith) (by omega_arith) (by omega_arith)) trivial) ?_
  -- The call.
  refine RelCT.seq (pw_wpQ (X' := fun W t => PReadyP e.L e.m₁ t ∧ CallArgs e.L W) (Q := PreOk e.L) q₁ q₂
    (pw_taint [] (by taint_decide) nopin) fun _ _ _ t V W hq _ _ hc R hS _ => ?_) ?_
  · have hS10 : Slots e.L (pubW e.L W) := hS.of fun j h1 _ _ => by
      simp only [pubW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]
    rw [Impl.RsaOaep.AArch64.Precomputed.pubArgs, pubArgs_eq, WP.block_append_iff, WP.block_append_iff]
    exact WP.mono (pubW_ok hL hP16 hc R hS) fun _ ⟨hc10, R10⟩ =>
      WP.mono (pubR_ok hL hP16 hc10 R10 hS10) fun _ ⟨hc11, hm11, hr11⟩ =>
        WP.mono (loads_ok hL hP16 hc11 hq hr11) fun _ ⟨hc12, hm12, hr12⟩ =>
          ⟨hc12, V, _, hm12 ▸ hm11 ▸ R10, hS10, readyP_of hq q₁ hr12, ⟨by simp [pubW, upd], by simp [pubW, upd]⟩⟩
  refine pdCallCT c fun t₁ t₂ ⟨_, _, hl, ⟨c₁, _, _, R₁, _, r₁, A₁⟩, ⟨c₂, _, _, R₂, _, r₂, A₂⟩⟩ => ?_
  have r₂' := readyP_of q₁ q₂ r₂
  obtain ⟨w, wl⟩ := pre_eq q₁ q₂
  have sa : ∀ {g vv m₀} {t : State} {V W}, Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W → CallArgs e.L W →
      stackArg t 0 = e.L.scr + BitVec.ofNat 64 8192 ∧ stackArg t 1 = e.L.sl - BitVec.ofNat 64 1024 :=
    fun hc R hA => ⟨by rw [stackArg, stackArgAddr, hc.sp]; exact (R.fr 0 (by unfold nW frameBytes; omega_arith)).trans hA.s0,
      by rw [stackArg, stackArgAddr, hc.sp]; exact (R.fr 1 (by unfold nW frameBytes; omega_arith)).trans hA.s1⟩
  refine ⟨pd_ok hL hP c₁ q₁ r₁ R₁ A₁, pd_ok hL hP c₂ q₂ r₂' R₂ A₂,
    ⟨c₁.sp.trans c₂.sp.symm, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [r₁.x0.trans r₂.x0.symm, r₁.x1.trans r₂.x1.symm, r₁.x2.trans r₂.x2.symm, r₁.x3.trans r₂.x3.symm,
      r₁.x4.trans r₂.x4.symm, r₁.x5.trans r₂.x5.symm, r₁.x6.trans r₂.x6.symm, r₁.x7.trans r₂.x7.symm]
  · rcases (by omega_arith : i = 0 ∨ i = 1) with rfl | rfl
    · rw [(sa c₁ R₁ A₁).1, (sa c₂ R₂ A₂).1]
    · rw [(sa c₁ R₁ A₁).2, (sa c₂ R₂ A₂).2]
  · have hx := hl.2.2 (PRE e.L e.m₁) (by rw [q₁.hx]; exact List.mem_singleton_self _)
    simp only [Nat.mul_div_cancel _ (by decide : 0 < 8)] at hx
    rw [r₁.x2, r₁.x3, r₂'.x2, r₂'.x3, pre_words hL c₁ q₁, pre_words hL c₂ q₂, ← w, ← wl, hx]
  · rw [r₁.x4, r₁.x5, r₂.x4, r₂.x5]
    have b₁ := c₁.bytes_ro hL (ro_E e.L)
    have b₂ := c₂.bytes_ro hL (ro_E e.L)
    simp only at b₁ b₂
    rw [b₁, b₂, hl.2.1]

end VG.Proof.RsaOaep.AArch64.Enc
