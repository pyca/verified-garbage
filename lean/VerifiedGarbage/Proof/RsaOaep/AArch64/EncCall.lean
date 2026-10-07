import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall

/-!
# RSAES-OAEP encryption on AArch64: the public-key operation

`pubArgs` (`pubW_ok`, `pubR_ok`) puts the rest of `scratch` in the frame's
words 0 and 1 and `vg_rsa_public_checked`'s registers: `out`, `n`, `e` and
`EM` (at the start of our working space) as the input. `pub_call` runs it:
`Ctx` holds again, and `out` holds the result for `EM` as it was.
-/

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Enc.AArch64 (PubImpl pubK)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce bytesAt_eq read8 write8)
open VG.Proof.RsaOaep.AArch64.Dec (sub_trans)

/-- The frame's words with the rest of `scratch` in words 0 and 1. -/
def pubW (L : ELay) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  upd (upd W 0 (L.scr + BitVec.ofNat 64 8192)) 1 (L.sl - BitVec.ofNat 64 1024)

theorem pubArgs_eq : pubArgs = (scrRsa .x10 ++ ([.ldrSp .x11 sScrLen, .subImm .x .x11 .x11 1024, .addSp .x9 0,
    .str .x .x10 .x9 0, .str .x .x11 .x9 8] : List Instr)) ++ (([.ldrSp .x0 sOut, .ldrSp .x1 sK, .ldrSp .x2 sN,
    .ldrSp .x3 sK, .ldrSp .x4 sE, .ldrSp .x5 sEl] : List Instr) ++ scr .x6 oEm ++ ([.ldrSp .x7 sK] : List Instr)) :=
  rfl

section
variable {L : ELay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem pubW_ok (hL : L.Ok) (hP : 16 ≤ L.P) (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W) :
    WP isa (.block (scrRsa .x10 ++ ([.ldrSp .x11 sScrLen, .subImm .x .x11 .x11 1024, .addSp .x9 0,
      .str .x .x10 .x9 0, .str .x .x11 .x9 8] : List Instr))) t fun u =>
        Ctx L g vv m₀ u ∧ Rep u.mem L.Q L.scr V (pubW L W) := by
  have Ly := hc.lay hL hP R hS.scr
  have G' := Ly.geo
  have h96 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 96) 8 := Ly.ld (d := 96) (by decide)
  have h192 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 192) 8 := Ly.ld (d := 192) (by decide)
  have w0 : InRegions t.wr L.Q 8 := by
    have := Ly.st (d := 0) (n := 8) (by decide); rwa [off, BitVec.add_zero] at this
  have w8 : InRegions t.wr (L.Q + BitVec.ofNat 64 8) 8 := Ly.st (d := 8) (by decide)
  have hs : t.mem.read (L.Q + BitVec.ofNat 64 96) 8 = L.scr := Ly.slot
  have hsl := R.rd8 (d := 192) (k := 24) rfl (by decide) hS.sl
  refine WP.mono (Q := fun (u : State) => u.mem = (t.mem.write L.Q 8 (L.scr + BitVec.ofNat 64 8192)).write
      (off L.Q 8) 8 (L.sl - BitVec.ofNat 64 1024) ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)) ?_
    fun u ⟨hm, hrd, hwr, hsp, hv, hcs⟩ => ?_
  · oaep_run [scrRsa, sScr, sScrLen, oRsa, h96, h192, w0, w8, Ly.sp, hs, hsl, BitVec.add_zero,
      imm16 (show 8192 < 65536 by decide)]
    oaep_fin
  have R' : Rep u.mem L.Q L.scr V (pubW L W) := by
    have R0 := R.wq G' (k := 0) (by decide) (L.scr + BitVec.ofNat 64 8192)
    rw [show off L.Q (8 * 0) = L.Q from BitVec.add_zero _] at R0
    rw [hm]; exact R0.wq G' (k := 1) (by decide) _
  have S : Step L.Q L.scr [] t u := ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], by
    have c0 := cF L.Q (d := 0) (n := 8) (by decide)
    rw [off, BitVec.add_zero] at c0
    rw [hm]
    exact Frame.write (Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ c0)
      (List.mem_cons_self ..) _ (cF L.Q (by decide))⟩
  exact ⟨hc.step hL hP S nil_ws, R'⟩

/-- The call's registers. -/
structure PReady (L : ELay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.out
  x1 : t.gpr .x1 = L.k
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.scr + BitVec.ofNat 64 0
  x7 : t.gpr .x7 = L.k

theorem pubR_ok (hL : L.Ok) (hP : 16 ≤ L.P) (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W) :
    WP isa (.block (([.ldrSp .x0 sOut, .ldrSp .x1 sK, .ldrSp .x2 sN, .ldrSp .x3 sK, .ldrSp .x4 sE,
      .ldrSp .x5 sEl] : List Instr) ++ scr .x6 oEm ++ ([.ldrSp .x7 sK] : List Instr))) t fun u =>
        Ctx L g vv m₀ u ∧ u.mem = t.mem ∧ PReady L u := by
  have Ly := hc.lay hL hP R hS.scr
  have h96 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 96) 8 := Ly.ld (d := 96) (by decide)
  have h152 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 152) 8 := Ly.ld (d := 152) (by decide)
  have h160 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 160) 8 := Ly.ld (d := 160) (by decide)
  have h168 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  have h176 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 176) 8 := Ly.ld (d := 176) (by decide)
  have h184 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 184) 8 := Ly.ld (d := 184) (by decide)
  have hs : t.mem.read (L.Q + BitVec.ofNat 64 96) 8 = L.scr := Ly.slot
  have ro := R.rd8 (d := 152) (k := 19) rfl (by decide) hS.out
  have rk := R.rd8 (d := 168) (k := 21) rfl (by decide) hS.k
  have rn := R.rd8 (d := 160) (k := 20) rfl (by decide) hS.n
  have re := R.rd8 (d := 176) (k := 22) rfl (by decide) hS.e
  have rel := R.rd8 (d := 184) (k := 23) rfl (by decide) hS.el
  refine WP.mono (Q := fun (u : State) => u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧ PReady L u) ?_
    fun u ⟨hm, hrd, hwr, hsp, hv, hcs, hr⟩ =>
      ⟨hc.step hL hP (Step.blk [] hrd hwr hsp hv hcs hm) nil_ws, hm, hr⟩
  oaep_run [scr, Mgf1.scr, Impl.RsaOaep.AArch64.lay, sScr, sK, sN, sE, sEl, sOut, oEm, h96, h152, h160, h168, h176,
    h184, Ly.sp, hs, ro, rk, rn, re, rel]
  refine ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, ?_⟩
  constructor <;> simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Size.bits, BitVec.setWidth_eq]

/-! ## The call -/

/-- The regions the call reads and writes. -/
abbrev pubRd (L : ELay) : List Region :=
  [L.N, L.E, ⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩, ⟨L.Q + BitVec.ofNat 64 0, 16⟩]
abbrev pubWr (L : ELay) : List Region :=
  [L.OUT, ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩]

theorem sl_sub (hL : L.Ok) : (L.sl - BitVec.ofNat 64 1024).toNat = L.sl.toNat - 1024 :=
  RsaPkcs1Enc.AArch64.Enc.toNat_sub_k (by have := hL.s8192; omega)

theorem scr8192 (hL : L.Ok) : (L.scr + BitVec.ofNat 64 8192).toNat = L.scr.toNat + 8192 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8192) (by decide)]
  have := hL.k64
  exact Nat.mod_eq_of_lt (by have := hL.bS; have := hL.s8192; unfold Spec.Rsa.scratchWords at *; omega)

/-- The call's stack arguments in the frame's first two words. -/
structure CallArgs (L : ELay) (W : Nat → BitVec 64) : Prop where
  s0 : W 0 = L.scr + BitVec.ofNat 64 8192
  s1 : W 1 = L.sl - BitVec.ofNat 64 1024

theorem pub_pre' (hL : L.Ok) {S : Nat} (hP : S + 1 ≤ L.P) (hc : Ctx L g vv m₀ t) (hr : PReady L t)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hA : CallArgs L W) :
    (pubK S).pre (t.callEntry.withRegions (pubRd L) (pubWr L)) := by
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hs8 := hL.s8192
  have hk := hL.k1024
  have hbS := hL.bS
  have hlow : Region.Sub ⟨L.Q - BitVec.ofNat 64 (S + 1), S + 1⟩ L.LOW := Offset.sub_below _ hP (by omega)
  have sa : ∀ i < 2, stackArg (t.callEntry.withRegions (pubRd L) (pubWr L)) i = W i := fun i hi => by
    rw [stackArg_ce, hc.sp]; exact R.fr i (by unfold nW frameBytes; omega)
  have a0 := (sa 0 (by decide)).trans hA.s0
  have a1 := (sa 1 (by decide)).trans hA.s1
  have aa : stackArgAddr (t.callEntry.withRegions (pubRd L) (pubWr L)) 0 = L.Q + BitVec.ofNat 64 0 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp]
  have arS : Region.Sub ⟨L.Q + BitVec.ofNat 64 0, 16⟩ L.STK := ELay.Ok.sub_stk (by omega)
  have lS := sub_trans hlow (ELay.Ok.low_stk (L := L))
  have hsl := sl_sub hL
  have hInp : Region.Sub ⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩ L.SCR := Offset.sub_base _ (by omega)
  have hScr : Region.Sub ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩ L.SCR :=
    Offset.sub_base _ (by rw [hsl]; omega)
  have dIS : Region.Disjoint ⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩
      ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩ :=
    Offset.disjoint L.scr (.inl (by omega)) (by omega) (by rw [hsl]; omega)
  simp only [pubK, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    hc.sp, gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    hr.x0, hr.x1, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, hr.x7, a0, a1, aa]
  refine ⟨by omega, by omega, trivial, trivial,
    hL.oR _ (ro_N L), hL.oR _ (ro_E L), hL.oS.sub_right hInp, hL.oS.sub_right hScr,
    (hL.kO.sub_left arS).symm,
    ((hL.sR _ (ro_N L)).sub_left hScr).symm, ((hL.sR _ (ro_E L)).sub_left hScr).symm, dIS,
    ((hL.kS.sub_left arS).symm.sub_left hScr),
    hL.kO.sub_left lS, (hL.kR _ (ro_N L)).sub_left lS, (hL.kR _ (ro_E L)).sub_left lS,
    (hL.kS.sub_left lS).sub_right hInp, (hL.kS.sub_left lS).sub_right hScr,
    (hL.fr_low (by omega)).symm.sub_left hlow,
    hL.bO, hL.bR _ (ro_N L), hL.bR _ (ro_E L), by rw [BitVec.add_zero]; omega,
    by rw [scr8192 hL, hsl]; omega,
    hL.kv, trivial, trivial, hL.el1, hL.elk,
    by rw [hsl]; have := hL.slk; unfold Spec.RsaPss.scratchWords at this; omega⟩

theorem covers_pub (hL : L.Ok) (hc : Ctx L g vv m₀ t) :
    Covers (pubRd L ++ pubWr L) (t.rd ++ t.wr) ∧ Covers (pubWr L) t.wr := by
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have hs8 := hL.s8192
  have hk := hL.k1024
  have hsl := sl_sub hL
  have c1 : ∃ off, L.scr + BitVec.ofNat 64 0 = L.SCR.base + BitVec.ofNat 64 off ∧ off + L.k.toNat ≤ L.SCR.len :=
    ⟨0, rfl, by show 0 + L.k.toNat ≤ L.sl.toNat * 8; omega⟩
  have c2 : ∃ off, L.scr + BitVec.ofNat 64 8192 = L.SCR.base + BitVec.ofNat 64 off ∧
      off + (L.sl - BitVec.ofNat 64 1024).toNat * 8 ≤ L.SCR.len :=
    ⟨8192, rfl, by show 8192 + _ ≤ L.sl.toNat * 8; rw [hsl]; omega⟩
  rw [hc.rd, hc.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [pubRd, pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.N, by simp, 0, z _, by simp⟩
    · exact ⟨L.E, by simp, 0, z _, by simp⟩
    · exact ⟨L.SCR, by simp, c1⟩
    · exact ⟨L.FR, by simp, 0, rfl, by show 0 + 16 ≤ frameBytes; decide⟩
    · exact ⟨L.OUT, by simp, 0, z _, by simp⟩
    · exact ⟨L.SCR, by simp, c2⟩
  · simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, 0, z _, by simp⟩
    · exact ⟨L.SCR, by simp, c2⟩

/-- After the call. -/
structure PCalled (L : ELay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (em : List Byte)
    (t' : State) : Prop where
  ctx : Ctx L g vv m₀ t'
  out : Spec.Rsa.written t'.mem L.out L.k.toNat ((t'.gpr .x0).setWidth 32)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat) em)

theorem pub_call (v : PubImpl) (hL : L.Ok) (hP : v.S + 1 ≤ L.P) (hP16 : 16 ≤ L.P) (hc : Ctx L g vv m₀ t)
    (hr : PReady L t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hA : CallArgs L W) :
    WP isa (.call v.name v.code) t
      (PCalled L g vv m₀ (Spec.Rsa.bytesAt t.mem (L.scr + BitVec.ofNat 64 0) L.k.toNat)) := by
  have hnQ := hL.nQ
  have hdp := v.depth'
  have hpQ := hL.pQ
  obtain ⟨hcov, hcovw⟩ := covers_pub hL hc
  have hs8 := hL.s8192
  have hk := hL.k1024
  have hsl := sl_sub hL
  refine WP.callFV v.correct (pub_pre' hL hP hc hr R hA) hcov hcovw
    (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  have hlow : Region.Sub (below t.sp (16 * v.code.aarch64Depth)) L.LOW := by
    rw [hc.sp]
    show Region.Sub _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
    exact Offset.sub_below _ (by omega) (by omega)
  have hws : ∀ r ∈ pubWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      Region.Sub r L.OUT ∨ Region.Sub r L.SCR ∨ Region.Sub r L.LOW := fun r hr => by
    simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl fun _ h => h
    · exact .inr (.inl (Offset.sub_base _ (by rw [hsl]; omega)))
    · exact .inr (.inr hlow)
  have hfr : ∀ d, d + 8 ≤ 328 → (d + 8 ≤ 288 ∨ 288 ≤ d) →
      ∀ X ∈ pubWr L ++ [below t.sp (16 * v.code.aarch64Depth)], Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ X :=
    fun d h₁ h₂ X hX => by
      rcases hws X hX with hs | hs | hs
      · rcases h₂ with h₂ | h₂
        · exact hL.stk_buf h₂ (.inl hs)
        · exact hL.args_buf h₂ h₁ (.inl hs)
      · rcases h₂ with h₂ | h₂
        · exact hL.stk_buf h₂ (.inr hs)
        · exact hL.args_buf h₂ h₁ (.inr hs)
      · exact (hL.fr_low h₁).sub_right hs
  have hk' : ∀ d, d + 8 ≤ 328 → (d + 8 ≤ 288 ∨ 288 ≤ d) →
      s'.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (hfr d h₁ h₂) (by decide)
  refine ⟨⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr h30 => (hcs r hr h30).trans (hc.cs r hr h30),
      fun r hr => (hvs r hr).trans (hc.vs r hr), (hk' 272 (by decide) (by decide)).trans hc.lr,
      fun j hj => (hk' _ (by omega) (by omega)).trans (hc.args j hj), hc.frame.trans (hf.sub fun r hr => by
        rcases hws r hr with hs | hs | hs
        · exact ⟨L.OUT, by simp, hs⟩
        · exact ⟨L.SCR, by simp, hs⟩
        · exact ⟨L.STK, by simp, fun x hx => (ELay.Ok.low_stk (L := L)) x (hs x hx)⟩)⟩, ?_⟩
  have hp := hpost
  simp only [pubK, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs),
    hr.x0, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6] at hp
  rw [hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_E L)] at hp
  exact hp

end

end VG.Proof.RsaOaep.AArch64.Enc
