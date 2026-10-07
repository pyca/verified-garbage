import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCTBase

/-!
# RSAES-OAEP encryption on AArch64: `EM` and the call in constant time

`encMain` from two runs in the same layout (`encMain_tr`): the copies into
`EM` from the registers their heads fix (`*E_pin`), the label's hash and
MGF1 as for any caller (`pw_lr`), the arguments' blocks by the taint
analysis, and the call of `vg_rsa_public_checked` with the same public
arguments in both runs (`pub_pub'`).
-/

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Enc.AArch64 (PubImpl pubK)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce)

/-- The call's public arguments agree in two runs in the same layout. -/
theorem pub_pub' {L : ELay} {S : Nat} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
    (hL : L.Ok) (hk : LeakEq L m₁ m₂) {a b : State} (ca : Ctx L g₁ v₁ m₁ a) (ra : PReady L a)
    {Va : Nat → Byte} {Wa : Nat → BitVec 64} (Ra : Rep a.mem L.Q L.scr Va Wa) (Aa : CallArgs L Wa)
    (cb : Ctx L g₂ v₂ m₂ b) (rb : PReady L b)
    {Vb : Nat → Byte} {Wb : Nat → BitVec 64} (Rb : Rep b.mem L.Q L.scr Vb Wb) (Ab : CallArgs L Wb) :
    (pubK S).pub (a.callEntry.withRegions (pubRd L) (pubWr L)) (b.callEntry.withRegions (pubRd L) (pubWr L)) := by
  have sa : ∀ i < 2, stackArg (a.callEntry.withRegions (pubRd L) (pubWr L)) i = Wa i := fun i hi => by
    rw [stackArg_ce, ca.sp]; exact Ra.fr i (by unfold nW frameBytes; omega)
  have sb : ∀ i < 2, stackArg (b.callEntry.withRegions (pubRd L) (pubWr L)) i = Wb i := fun i hi => by
    rw [stackArg_ce, cb.sp]; exact Rb.fr i (by unfold nW frameBytes; omega)
  have na := ca.bytes_ro hL (ro_N L)
  have nb := cb.bytes_ro hL (ro_N L)
  have ea := ca.bytes_ro hL (ro_E L)
  have eb := cb.bytes_ro hL (ro_E L)
  simp only at na nb ea eb
  simp only [pubK, State.withRegions_sp, State.callEntry_sp, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ra.x0, ra.x1, ra.x2, ra.x3, ra.x4, ra.x5, ra.x6, ra.x7, rb.x0, rb.x1, rb.x2, rb.x3, rb.x4, rb.x5, rb.x6,
    rb.x7, ca.sp, cb.sp, na, nb, ea, eb, sa 0 (by decide), sa 1 (by decide), sb 0 (by decide),
    sb 1 (by decide), Aa.s0, Aa.s1, Ab.s0, Ab.s1, true_and]
  exact hk

theorem putMsg_eq : putMsg = .seq (.block ((([.ldrSp .x11 sMsg] : List Instr) ++ scr .x12 oEm ++
    ([.ldrSp .x10 sK, .add .x .x12 .x12 .x10, .ldrSp .x13 sMsgLen, .sub .x .x12 .x12 .x13,
      .subImm .x .x12 .x12 1] : List Instr)) ++
    ([.movz .x .x10 1 0, .strb .x10 .x12 0, .addImm .x .x12 .x12 1] : List Instr)))
    (.ite (.nonzero .x .x13) copyLoop (.block [])) := rfl

variable {Hl Gm : Hash} (hH : StreamOK Hl.stream) (hG : StreamOK Gm.stream)

include hH hG in
theorem encMain_tr {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D) (hGv : Proof.Mgf1.Valid Gs) (pv : PubImpl)
    {P : Nat} {e : Env} (hL : e.L.Ok) (hP : pv.S + 1 ≤ e.L.P) (hP16 : 16 ≤ e.L.P) (hD : e.L.D = Hl.D)
    (hk : 2 * Hl.D + 2 + e.L.ml.toNat ≤ e.L.k.toNat) :
    RelCT isa (PW P e fun _ _ => True) (encMain Hl Gm pv.name pv.code) fun _ _ => True := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  replace hD0 : 0 < Hl.D := hD0
  have hk1024 := hL.k1024
  have cSt : oSt = 3072 := rfl
  have cR : oRsa = 8192 := rfl
  have f4 : MFit 1 Hl.D (1 + Hl.D) (e.L.k.toNat - Hl.D - 1) :=
    ⟨by rw [cSt]; omega, by rw [cSt]; omega, by omega, by omega, by omega⟩
  have f2 : MFit (1 + Hl.D) (e.L.k.toNat - Hl.D - 1) 1 Hl.D :=
    ⟨by rw [cSt]; omega, by rw [cSt]; omega, by omega, by omega, by omega⟩
  have ly : ∀ {g vv m₀} {t : State} {V W}, Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W → Slots e.L W →
      Lay t e.L.Q e.L.scr := fun hc R hS => hc.lay hL hP16 R hS.scr
  have hk3 : ∀ {W : Nat → BitVec 64}, Slots e.L W → W 21 = BitVec.ofNat 64 e.L.k.toNat := fun hS => by
    rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm3 : ∀ {W : Nat → BitVec 64}, Slots e.L W → W 28 = BitVec.ofNat 64 e.L.ml.toNat := fun hS => by
    rw [hS.ml, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- The seed's and the message's bytes are apart from our working space.
  have hsdS : ∀ i < Hl.D, ∀ j < oRsa, off e.L.sd i ≠ off e.L.scr j := fun i hi j hj
      (h' : e.L.sd + BitVec.ofNat 64 i = e.L.scr + BitVec.ofNat 64 j) =>
    (hL.sR _ (ro_SD e.L)) _ (hL.ours_scr _ (Offset.contains_base e.L.scr (d := j) (n := 1) (by omega) (by omega)))
      (h' ▸ Offset.contains_base e.L.sd (d := i) (n := 1) (k := e.L.D) (by omega)
        (by have := hL.bR _ (ro_SD e.L); simp only at this; omega))
  have hmsS : ∀ i < e.L.ml.toNat, ∀ j < oRsa, off e.L.msg i ≠ off e.L.scr j := fun i hi j hj
      (h' : e.L.msg + BitVec.ofNat 64 i = e.L.scr + BitVec.ofNat 64 j) =>
    (hL.sR _ (ro_MSG e.L)) _ (hL.ours_scr _ (Offset.contains_base e.L.scr (d := j) (n := 1) (by omega) (by omega)))
      (h' ▸ Offset.contains_base e.L.msg (d := i) (n := 1) (k := e.L.ml.toNat) (by omega)
        (by have := hL.bR _ (ro_MSG e.L); simp only at this; omega))
  have inRd : ∀ {g vv m₀} {u : State} {R : Region}, Ctx e.L g vv m₀ u →
      R ∈ [e.L.N, e.L.E, e.L.LAB, e.L.MSG, e.L.SD, e.L.ARGS] →
      ∀ {a : Addr} {n : Nat}, R.Contains a n → InRegions (u.rd ++ u.wr) a n := fun hcu hR _ _ h3 =>
    ⟨_, List.mem_append_left _ (by rw [hcu.rd]; exact hR), h3⟩
  simp only [encMain, encEm, seqs]
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
        (fun i hi => inRd hc (by simp) (Offset.contains_base e.L.sd (d := i) (n := 1) (k := e.L.D) (by omega)
          (by have := hL.bR _ (ro_SD e.L); simp only at this; omega)))
        (fun i hi j hj => hsdS i hi _ (by unfold oEm; omega)))
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
          fun _ _ _ _ _ _ _ _ hc R hS _ => msgE_pin (ly hc R hS) R (hk3 hS) (hm3 hS) hS.msg (by omega)))
      fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (putMsg_ok (ly hc R hS) R (hk3 hS) (hm3 hS) hS.msg (by omega)
        hk1024 (fun i hi => inRd hc (by simp) (Offset.contains_base e.L.msg (d := i) (n := 1) (k := e.L.ml.toNat)
          (by omega) (by have := hL.bR _ (ro_MSG e.L); simp only at this; omega))) hmsS)
        fun _ ⟨_, Su, Ru⟩ => In.of_step hL hP16 hc Su nil_ws Ru hS trivial
  -- `DB` masked.
  refine RelCT.seq (pw_blk (X' := fun W _ => MArgs W e.L.scr 1 Hl.D (1 + Hl.D) (e.L.k.toNat - Hl.D - 1)) []
    (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (dbArgs gH)) (by rfl) (by taint_decide)) nopin
    fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (dbArgs_ok (ly hc R hS) R (hk3 hS) (by omega) (by omega) hk1024 [])
      fun _ ⟨_, Su, Ru⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega)) (mW_args _ _ _ _ _ _)) ?_
  refine RelCT.seq (pw_wp (X' := fun _ _ => True) (pw_lr hP16 (mgfXor_tr hG f4 fun _ _ h => h)
      fun _ _ _ _ _ _ _ _ x => x)
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (mgfXor_ok hG hGh hGl hGv (ly hc R hS) R f4 hx)
      fun _ ⟨_, Su, _, W', Ru, hW', _⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ h2 h3 => hW' j (by unfold nW frameBytes; omega) (by omega) (by omega)) trivial) ?_
  -- The seed masked.
  refine RelCT.seq (pw_blk (X' := fun W _ => MArgs W e.L.scr (1 + Hl.D) (e.L.k.toNat - Hl.D - 1) 1 Hl.D) []
    (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (seedArgs gH)) (by rfl) (by taint_decide)) nopin
    fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (seedArgs_ok (ly hc R hS) R (hk3 hS) (by omega) (by omega) hk1024 [])
      fun _ ⟨_, Su, Ru⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega)) (mW_args _ _ _ _ _ _)) ?_
  refine RelCT.seq (pw_wp (X' := fun _ _ => True) (pw_lr hP16 (mgfXor_tr hG f2 fun _ _ h => h)
      fun _ _ _ _ _ _ _ _ x => x)
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (mgfXor_ok hG hGh hGl hGv (ly hc R hS) R f2 hx)
      fun _ ⟨_, Su, _, W', Ru, hW', _⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ h2 h3 => hW' j (by unfold nW frameBytes; omega) (by omega) (by omega)) trivial) ?_
  -- The call.
  refine RelCT.seq (pw_blk (X' := fun W t => PReady e.L t ∧ CallArgs e.L W) [] (by taint_decide) nopin
    fun _ _ _ t V W _ _ hc R hS _ => ?_) ?_
  · have hS10 : Slots e.L (pubW e.L W) := hS.of fun j h1 _ _ => by
      simp only [pubW, upd]; rw [ifn (by omega), ifn (by omega)]
    rw [pubArgs_eq, WP.block_append_iff]
    exact WP.mono (pubW_ok hL hP16 hc R hS) fun _ ⟨hc10, R10⟩ =>
      WP.mono (pubR_ok hL hP16 hc10 R10 hS10) fun _ ⟨hc11, hm11, hr11⟩ =>
        ⟨hc11, V, _, hm11 ▸ R10, hS10, hr11, ⟨by simp [pubW, upd], by simp [pubW, upd]⟩⟩
  exact RelCT.call (n := pv.name) pv.correct pv.ct (pubRd e.L) (pubWr e.L)
    fun _ _ ⟨_, _, hl, ⟨ca, _, _, Ra, _, ra, Aa⟩, ⟨cb, _, _, Rb, _, rb, Ab⟩⟩ =>
      ⟨pub_pre' hL hP ca ra Ra Aa, pub_pre' hL hP cb rb Rb Ab, pub_pub' hL hl ca ra Ra Aa cb rb Rb Ab,
        (covers_pub hL ca).1, (covers_pub hL ca).2, (covers_pub hL cb).1, (covers_pub hL cb).2⟩

end VG.Proof.RsaOaep.AArch64.Enc
