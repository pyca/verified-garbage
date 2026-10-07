import VerifiedGarbage.Proof.RsaOaep.AArch64.DecEntry
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall

/-!
# RSAES-OAEP decryption on AArch64: the private-key operation

`privArgs` (`privW_ok`, `privR_ok`) puts the rest of `scratch` in the frame's
words 10 and 11 and `vg_rsa_private_checked`'s registers: `EM`'s place at
the start of our working space (`k` bytes), `n`, `e` and the ciphertext.
`priv_call` runs it: `Ctx` holds again, the frame's words are as they were,
and `EM`'s place holds `EM` (or zeros) as `privOut` says.
-/

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Enc.AArch64 (PrivImpl privK)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce bytesAt_eq read8 write8)

namespace Ctx

variable {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
  (hc : Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

/-- A byte of a buffer the function only reads, as on entry. -/
theorem byte_ro {R : Region} (hR : R ∈ L.ro) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  hc.frame.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [(hL.oR R hR).symm, (hL.mR R hR).symm, (hL.sR R hR).symm, (hL.kR R hR).symm])
    (by have := hL.bR R hR; omega) hi

/-- The bytes of a buffer the function only reads, as on entry. -/
theorem bytes_ro {R : Region} (hR : R ∈ L.ro) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt m₀ R.base R.len :=
  bytesAt_eq fun _ hi => hc.byte_ro hL hR hi

end Ctx

/-! ## The arguments -/

/-- The frame's words with the rest of `scratch` in words 10 and 11. -/
def privW (L : DLay) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  upd (upd W 10 (L.scr + BitVec.ofNat 64 8192)) 11 (L.sl - BitVec.ofNat 64 1024)

theorem privArgs_eq : privArgs = (scrRsa .x10 ++ ([.ldrSp .x11 sScrLen, .subImm .x .x11 .x11 1024,
    .str .x .x10 .x9 80, .str .x .x11 .x9 88] : List Instr)) ++ (scr .x0 oEm ++ ([.ldrSp .x1 sK, .ldrSp .x2 sN,
    .ldrSp .x3 sK, .ldrSp .x4 sE, .ldrSp .x5 sEl, .ldrSp .x6 (arg 11), .ldrSp .x7 sK] : List Instr)) := rfl

section
variable {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem privW_ok (hL : L.Ok) (hP : 16 ≤ L.P) (hc : Ctx L g vv m₀ t) (h9 : t.gpr .x9 = L.Q) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W) :
    WP isa (.block (scrRsa .x10 ++ ([.ldrSp .x11 sScrLen, .subImm .x .x11 .x11 1024, .str .x .x10 .x9 80,
      .str .x .x11 .x9 88] : List Instr))) t fun u =>
        Ctx L g vv m₀ u ∧ u.gpr .x9 = L.Q ∧ Rep u.mem L.Q L.scr V (privW L W) := by
  have Ly := hc.lay hL hP R hS.scr
  have G' := Ly.geo
  have h96 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 96) 8 := Ly.ld (d := 96) (by decide)
  have h192 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 192) 8 := Ly.ld (d := 192) (by decide)
  have w80 : InRegions t.wr (L.Q + BitVec.ofNat 64 80) 8 := Ly.st (d := 80) (by decide)
  have w88 : InRegions t.wr (L.Q + BitVec.ofNat 64 88) 8 := Ly.st (d := 88) (by decide)
  have hs : t.mem.read (L.Q + BitVec.ofNat 64 96) 8 = L.scr := Ly.slot
  have hsl := R.rd8 (d := 192) (k := 24) rfl (by decide) hS.sl
  refine WP.mono (Q := fun (u : State) => u.mem = (t.mem.write (off L.Q 80) 8 (L.scr + BitVec.ofNat 64 8192)).write
      (off L.Q 88) 8 (L.sl - BitVec.ofNat 64 1024) ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧
      u.gpr .x9 = t.gpr .x9 ∧ (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)) ?_
    fun u ⟨hm, hrd, hwr, hsp, hv, hx9, hcs⟩ => ?_
  · oaep_run [scrRsa, sScr, sScrLen, oRsa, h9, h96, h192, w80, w88, Ly.sp, hs, hsl,
      imm16 (show 8192 < 65536 by decide)]
    oaep_fin
  have R' : Rep u.mem L.Q L.scr V (privW L W) := by
    rw [hm]; exact (R.wq G' (k := 10) (by decide) _).wq G' (k := 11) (by decide) _
  have S : Step L.Q L.scr [] t u := ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], by
    rw [hm]
    exact Frame.write (Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF L.Q (by decide)))
      (List.mem_cons_self ..) _ (cF L.Q (by decide))⟩
  exact ⟨hc.step hL hP S fun r h => absurd h List.not_mem_nil, hx9.trans h9, R'⟩

/-- The call's registers. -/
structure Ready (L : DLay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.scr + BitVec.ofNat 64 0
  x1 : t.gpr .x1 = L.k
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.ct
  x7 : t.gpr .x7 = L.k

theorem privR_ok (hL : L.Ok) (hP : 16 ≤ L.P) (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W) :
    WP isa (.block (scr .x0 oEm ++ ([.ldrSp .x1 sK, .ldrSp .x2 sN, .ldrSp .x3 sK, .ldrSp .x4 sE, .ldrSp .x5 sEl,
      .ldrSp .x6 (arg 11), .ldrSp .x7 sK] : List Instr))) t fun u =>
        Ctx L g vv m₀ u ∧ u.mem = t.mem ∧ Ready L u := by
  have Ly := hc.lay hL hP R hS.scr
  have h96 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 96) 8 := Ly.ld (d := 96) (by decide)
  have h160 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 160) 8 := Ly.ld (d := 160) (by decide)
  have h168 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  have h176 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 176) 8 := Ly.ld (d := 176) (by decide)
  have h184 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 184) 8 := Ly.ld (d := 184) (by decide)
  have h376 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 376) 8 :=
    ⟨L.ARGS, by rw [hc.rd]; simp, Offset.contains _ (by decide) (by decide) (by have := hL.nQ; omega)⟩
  have hs : t.mem.read (L.Q + BitVec.ofNat 64 96) 8 = L.scr := Ly.slot
  have rk := R.rd8 (d := 168) (k := 21) rfl (by decide) hS.k
  have rn := R.rd8 (d := 160) (k := 20) rfl (by decide) hS.n
  have re := R.rd8 (d := 176) (k := 22) rfl (by decide) hS.e
  have rel := R.rd8 (d := 184) (k := 23) rfl (by decide) hS.el
  have rct : t.mem.read (L.Q + BitVec.ofNat 64 376) 8 = L.ct := by rw [read8]; exact hc.args 11 (by decide)
  refine WP.mono (Q := fun (u : State) => u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧ Ready L u) ?_
    fun u ⟨hm, hrd, hwr, hsp, hv, hcs, hr⟩ =>
      ⟨hc.step hL hP (Step.blk [] hrd hwr hsp hv hcs hm) fun r h => absurd h List.not_mem_nil, hm, hr⟩
  oaep_run [scr, Mgf1.scr, Impl.RsaOaep.AArch64.lay, sScr, sK, sN, sE, sEl, arg, frameBytes, oEm, h96, h160, h168, h176, h184, h376,
    Ly.sp, hs, rk, rn, re, rel, rct]
  refine ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, ?_⟩
  constructor <;> simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Size.bits, BitVec.setWidth_eq]

end

/-! ## The call -/

/-- The regions the call reads and writes. -/
abbrev privRd (L : DLay) : List Region :=
  [L.N, L.E, L.CT, L.PP, L.QQ, L.DP, L.DQ, L.QI, ⟨L.Q + BitVec.ofNat 64 0, 96⟩]
abbrev privWr (L : DLay) : List Region :=
  [⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩, ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩]

/-- What the private-key operation gives, from the buffers on entry. -/
def privOut (L : DLay) (m₀ : Mem) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
    (Spec.Rsa.bytesAt m₀ L.ct L.k.toNat) (Spec.Rsa.bytesAt m₀ L.p L.pl.toNat)
    (Spec.Rsa.bytesAt m₀ L.q L.ql.toNat) (Spec.Rsa.bytesAt m₀ L.dp L.pl.toNat)
    (Spec.Rsa.bytesAt m₀ L.dq L.ql.toNat) (Spec.Rsa.bytesAt m₀ L.qi L.pl.toNat)

/-- The private-key operation's stack arguments in the frame's first twelve
words. -/
structure CallArgs (L : DLay) (W : Nat → BitVec 64) : Prop where
  p : W 0 = L.p
  args : ∀ j < 9, W (j + 1) = ourArg L j
  s10 : W 10 = L.scr + BitVec.ofNat 64 8192
  s11 : W 11 = L.sl - BitVec.ofNat 64 1024

section
variable {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem sl_sub (hL : L.Ok) : (L.sl - BitVec.ofNat 64 1024).toNat = L.sl.toNat - 1024 :=
  RsaPkcs1Enc.AArch64.Enc.toNat_sub_k (by have := hL.s8192; omega)

theorem scr8192 (hL : L.Ok) : (L.scr + BitVec.ofNat 64 8192).toNat = L.scr.toNat + 8192 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8192) (by decide)]
  have := hL.k64
  exact Nat.mod_eq_of_lt (by have := hL.bS; have := hL.s8192; unfold Spec.Rsa.scratchWords at *; omega)

theorem priv_pre' (hL : L.Ok) {S : Nat} (hP : L.P = S + 1) (hc : Ctx L g vv m₀ t) (hr : Ready L t)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hA : CallArgs L W) :
    (privK S).pre (t.callEntry.withRegions (privRd L) (privWr L)) := by
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hs8 := hL.s8192
  have hk := hL.k1024
  have hbS := hL.bS
  rw [hP] at hpQ
  have hlow : (⟨L.Q - BitVec.ofNat 64 (S + 1), S + 1⟩ : Region) = L.LOW := by
    show _ = (⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩ : Region); rw [hP]
  have sa : ∀ i < 12, stackArg (t.callEntry.withRegions (privRd L) (privWr L)) i = W i := fun i hi => by
    rw [stackArg_ce, hc.sp]; exact R.fr i (by unfold nW frameBytes; omega)
  have a0 := (sa 0 (by decide)).trans hA.p
  have a1 := (sa 1 (by decide)).trans (hA.args 0 (by decide))
  have a2 := (sa 2 (by decide)).trans (hA.args 1 (by decide))
  have a3 := (sa 3 (by decide)).trans (hA.args 2 (by decide))
  have a4 := (sa 4 (by decide)).trans (hA.args 3 (by decide))
  have a5 := (sa 5 (by decide)).trans (hA.args 4 (by decide))
  have a6 := (sa 6 (by decide)).trans (hA.args 5 (by decide))
  have a7 := (sa 7 (by decide)).trans (hA.args 6 (by decide))
  have a8 := (sa 8 (by decide)).trans (hA.args 7 (by decide))
  have a9 := (sa 9 (by decide)).trans (hA.args 8 (by decide))
  have a10 := (sa 10 (by decide)).trans hA.s10
  have a11 := (sa 11 (by decide)).trans hA.s11
  simp only [ourArg] at a1 a2 a3 a4 a5 a6 a7 a8 a9
  have aa : stackArgAddr (t.callEntry.withRegions (privRd L) (privWr L)) 0 = L.Q + BitVec.ofNat 64 0 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp]
  have arS : Region.Sub ⟨L.Q + BitVec.ofNat 64 0, 96⟩ L.STK := DLay.Ok.sub_stk (by omega)
  have lS := DLay.Ok.low_stk (L := L)
  have hsl := sl_sub hL
  have hOut : Region.Sub ⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩ L.SCR := Offset.sub_base _ (by omega)
  have hScr : Region.Sub ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩ L.SCR :=
    Offset.sub_base _ (by rw [hsl]; omega)
  have dOS : Region.Disjoint ⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩
      ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩ :=
    Offset.disjoint L.scr (.inl (by omega)) (by omega) (by rw [hsl]; omega)
  simp only [privK, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    hc.sp, gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    hr.x0, hr.x1, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, hr.x7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    aa, hlow, hL.dpl, hL.qil, hL.dql]
  refine ⟨by omega, by omega, trivial, trivial,
    (hL.sR _ (ro_N L)).sub_left hOut, (hL.sR _ (ro_E L)).sub_left hOut, (hL.sR _ (ro_CT L)).sub_left hOut,
    (hL.sR _ (ro_PP L)).sub_left hOut, (hL.sR _ (ro_QQ L)).sub_left hOut, (hL.sR _ (ro_DP L)).sub_left hOut,
    (hL.sR _ (ro_DQ L)).sub_left hOut, (hL.sR _ (ro_QI L)).sub_left hOut, dOS,
    ((hL.kS.sub_left arS).symm.sub_left hOut),
    ((hL.sR _ (ro_N L)).sub_left hScr).symm, ((hL.sR _ (ro_E L)).sub_left hScr).symm,
    ((hL.sR _ (ro_CT L)).sub_left hScr).symm, ((hL.sR _ (ro_PP L)).sub_left hScr).symm,
    ((hL.sR _ (ro_QQ L)).sub_left hScr).symm, ((hL.sR _ (ro_DP L)).sub_left hScr).symm,
    ((hL.sR _ (ro_DQ L)).sub_left hScr).symm, ((hL.sR _ (ro_QI L)).sub_left hScr).symm,
    ((hL.kS.sub_left arS).symm.sub_left hScr),
    (hL.kS.sub_left lS).sub_right hOut, (hL.kR _ (ro_N L)).sub_left lS, (hL.kR _ (ro_E L)).sub_left lS,
    (hL.kR _ (ro_CT L)).sub_left lS, (hL.kR _ (ro_PP L)).sub_left lS, (hL.kR _ (ro_QQ L)).sub_left lS,
    (hL.kR _ (ro_DP L)).sub_left lS, (hL.kR _ (ro_DQ L)).sub_left lS, (hL.kR _ (ro_QI L)).sub_left lS,
    (hL.kS.sub_left lS).sub_right hScr, (hL.fr_low (by omega)).symm,
    by rw [BitVec.add_zero]; omega, hL.bR _ (ro_N L), hL.bR _ (ro_E L), hL.bR _ (ro_CT L), hL.bR _ (ro_PP L),
    hL.bR _ (ro_QQ L), hL.bR _ (ro_DP L), hL.bR _ (ro_DQ L), hL.bR _ (ro_QI L),
    by rw [scr8192 hL, hsl]; omega,
    hL.kv, trivial, trivial, hL.el1, hL.elk, hL.pl1, hL.plk, hL.ql1, hL.qlk, trivial, trivial, trivial,
    by rw [hsl]; have := hL.slk; unfold Spec.RsaPss.scratchWords at this; omega⟩

theorem covers_priv (hL : L.Ok) (hc : Ctx L g vv m₀ t) :
    Covers (privRd L ++ privWr L) (t.rd ++ t.wr) ∧ Covers (privWr L) t.wr := by
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
  · simp only [privRd, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.N, by simp, 0, z _, by simp⟩
    · exact ⟨L.E, by simp, 0, z _, by simp⟩
    · exact ⟨L.CT, by simp, 0, z _, by simp⟩
    · exact ⟨L.PP, by simp, 0, z _, by simp⟩
    · exact ⟨L.QQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.DP, by simp, 0, z _, by simp⟩
    · exact ⟨L.DQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.QI, by simp, 0, z _, by simp⟩
    · exact ⟨L.FR, by simp, 0, rfl, by show 0 + 96 ≤ frameBytes; decide⟩
    · exact ⟨L.SCR, by simp, c1⟩
    · exact ⟨L.SCR, by simp, c2⟩
  · simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.SCR, by simp, c1⟩
    · exact ⟨L.SCR, by simp, c2⟩

/-- After the call. -/
structure Called (L : DLay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (W : Nat → BitVec 64)
    (t' : State) : Prop where
  ctx : Ctx L g vv m₀ t'
  rep : Rep t'.mem L.Q L.scr (fun o => t'.mem (off L.scr o)) W
  out : Spec.Rsa.writtenOutcome t'.mem (L.scr + BitVec.ofNat 64 0) L.k.toNat ((t'.gpr .x0).setWidth 32)
    (privOut L m₀)

theorem priv_call (v : PrivImpl) (hL : L.Ok) (hP : L.P = v.S + 1) (hc : Ctx L g vv m₀ t) (hr : Ready L t)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hA : CallArgs L W) :
    WP isa (.call v.name v.code) t (Called L g vv m₀ W) := by
  have hnQ := hL.nQ
  have hdp := v.depth'
  have hpQ := hL.pQ
  rw [hP] at hpQ
  obtain ⟨hcov, hcovw⟩ := covers_priv hL hc
  have hs8 := hL.s8192
  have hk := hL.k1024
  have hsl := sl_sub hL
  refine WP.callFV v.correct (priv_pre' hL hP hc hr R hA) hcov hcovw
    (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  -- What the call may change: our working space, the rest of `scratch` and the stack below the frame.
  have hlow : Region.Sub (below t.sp (16 * v.code.aarch64Depth)) L.LOW := by
    rw [hc.sp]
    show Region.Sub _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
    rw [hP]; exact Offset.sub_below _ hdp (by omega)
  have hws : ∀ r ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      Region.Sub r L.SCR ∨ Region.Sub r L.LOW := fun r hr => by
    simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Offset.sub_base _ (by omega))
    · exact .inl (Offset.sub_base _ (by rw [hsl]; omega))
    · exact .inr hlow
  have hfr : ∀ d, d + 8 ≤ 408 → (d + 8 ≤ 288 ∨ 288 ≤ d) →
      ∀ X ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)], Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ X :=
    fun d h₁ h₂ X hX => by
      rcases hws X hX with hs | hs
      · rcases h₂ with h₂ | h₂
        · exact hL.stk_buf h₂ (.inr (.inr hs))
        · exact hL.args_buf h₂ h₁ (.inr (.inr hs))
      · exact (hL.fr_low h₁).sub_right hs
  have hk' : ∀ d, d + 8 ≤ 408 → (d + 8 ≤ 288 ∨ 288 ≤ d) →
      s'.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (hfr d h₁ h₂) (by decide)
  have hc' : Ctx L g vv m₀ s' :=
    ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr h30 => (hcs r hr h30).trans (hc.cs r hr h30),
      fun r hr => (hvs r hr).trans (hc.vs r hr), (hk' 272 (by decide) (by decide)).trans hc.lr,
      fun j hj => (hk' _ (by omega) (by omega)).trans (hc.args j hj), hc.frame.trans (hf.sub fun r hr => by
        rcases hws r hr with hs | hs
        · exact ⟨L.SCR, by simp, hs⟩
        · exact ⟨L.STK, by simp, fun x hx => (DLay.Ok.low_stk (L := L)) x (hs x hx)⟩)⟩
  refine ⟨hc', ⟨fun _ _ => rfl, fun j hj => ?_⟩, ?_⟩
  · have : 8 * j + 8 ≤ 272 := by unfold nW frameBytes at hj; omega
    exact (hk' (8 * j) (by omega) (.inl (by omega))).trans (R.fr j hj)
  have sa : ∀ i < 12, stackArg (t.callEntry.withRegions (privRd L) (privWr L)) i = W i := fun i hi => by
    rw [stackArg_ce, hc.sp]; exact R.fr i (by unfold nW frameBytes; omega)
  have a0 := (sa 0 (by decide)).trans hA.p
  have a1 := (sa 1 (by decide)).trans (hA.args 0 (by decide))
  have a2 := (sa 2 (by decide)).trans (hA.args 1 (by decide))
  have a3 := (sa 3 (by decide)).trans (hA.args 2 (by decide))
  have a4 := (sa 4 (by decide)).trans (hA.args 3 (by decide))
  have a6 := (sa 6 (by decide)).trans (hA.args 5 (by decide))
  have a8 := (sa 8 (by decide)).trans (hA.args 7 (by decide))
  simp only [ourArg] at a1 a2 a3 a4 a6 a8
  have hp := hpost
  simp only [privK, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs),
    hr.x0, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, a0, a1, a2, a3, a4, a6, a8] at hp
  rw [hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_E L), hc.bytes_ro hL (ro_CT L), hc.bytes_ro hL (ro_PP L),
    hc.bytes_ro hL (ro_QQ L), hc.bytes_ro hL (ro_DP L), hc.bytes_ro hL (ro_DQ L), hc.bytes_ro hL (ro_QI L)] at hp
  exact hp

end

end VG.Proof.RsaOaep.AArch64.Dec
