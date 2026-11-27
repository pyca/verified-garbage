module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecEntry
import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
public import VerifiedGarbage.Proof.HashTable.AArch64
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCallee
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `RsaOaep.AArch64.DecPriv`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on AArch64: the private-key operation

`privArgs` (`privW_ok`, `privR_ok`) puts the rest of `scratch` in the frame's
words 10 and 11 and `vg_rsa_private_checked`'s registers: `EM`'s place at
the start of our working space (`k` bytes), `n`, `e` and the ciphertext.
`priv_call` runs it: `Ctx` holds again, the frame's words are as they were,
and `EM`'s place holds `EM` (or zeros) as `privOut` says.
-/

@[expose] public section

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
    (by have := hL.bR R hR; omega_arith) hi

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
  obtain Ly := hc.lay hL hP R hS.scr
  have G' := Ly.geo
  obtain h96 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 96) 8 := Ly.ld (d := 96) (by decide)
  obtain h192 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 192) 8 := Ly.ld (d := 192) (by decide)
  obtain w80 : InRegions t.wr (L.Q + BitVec.ofNat 64 80) 8 := Ly.st (d := 80) (by decide)
  obtain w88 : InRegions t.wr (L.Q + BitVec.ofNat 64 88) 8 := Ly.st (d := 88) (by decide)
  have hs : t.mem.read (L.Q + BitVec.ofNat 64 96) 8 = L.scr := Ly.slot
  obtain hsl := R.rd8 (d := 192) (k := 24) rfl (by decide) hS.sl
  refine WP.mono (Q := fun (u : State) => u.mem = (t.mem.write (off L.Q 80) 8 (L.scr + BitVec.ofNat 64 8192)).write
      (off L.Q 88) 8 (L.sl - BitVec.ofNat 64 1024) ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧
      u.gpr .x9 = t.gpr .x9 ∧ (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)) ?_
    fun u ⟨hm, hrd, hwr, hsp, hv, hx9, hcs⟩ => ?_
  · oaep_run [scrRsa, sScr, sScrLen, oRsa, h9, h96, h192, w80, w88, Ly.sp, hs, hsl,
      imm16 (show 8192 < 65536 by decide)]
    oaep_fin
  obtain R' : Rep u.mem L.Q L.scr V (privW L W) := by
    rw [hm]; exact (R.wq G' (k := 10) (by decide) _).wq G' (k := 11) (by decide) _
  obtain S : Step L.Q L.scr [] t u := ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], by
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
  obtain Ly := hc.lay hL hP R hS.scr
  obtain h96 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 96) 8 := Ly.ld (d := 96) (by decide)
  obtain h160 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 160) 8 := Ly.ld (d := 160) (by decide)
  obtain h168 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  obtain h176 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 176) 8 := Ly.ld (d := 176) (by decide)
  obtain h184 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 184) 8 := Ly.ld (d := 184) (by decide)
  obtain h376 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 376) 8 :=
    ⟨L.ARGS, by rw [hc.rd]; simp, Offset.contains _ (by decide) (by have := hL.al136; omega_arith)
      (by have := hL.al152; omega_arith)⟩
  have hs : t.mem.read (L.Q + BitVec.ofNat 64 96) 8 = L.scr := Ly.slot
  obtain rk := R.rd8 (d := 168) (k := 21) rfl (by decide) hS.k
  obtain rn := R.rd8 (d := 160) (k := 20) rfl (by decide) hS.n
  obtain re := R.rd8 (d := 176) (k := 22) rfl (by decide) hS.e
  obtain rel := R.rd8 (d := 184) (k := 23) rfl (by decide) hS.el
  obtain rct : t.mem.read (L.Q + BitVec.ofNat 64 376) 8 = L.ct := by rw [read8]; exact hc.args 11 (by decide)
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
  RsaPkcs1Enc.AArch64.Enc.toNat_sub_k (by have := hL.s8192; omega_arith)

theorem scr8192 (hL : L.Ok) : (L.scr + BitVec.ofNat 64 8192).toNat = L.scr.toNat + 8192 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8192) (by decide)]
  have := hL.k64
  exact Nat.mod_eq_of_lt (by have := hL.bS; have := hL.s8192; unfold Spec.Rsa.scratchWords at *; omega_arith)

theorem priv_pre' (hL : L.Ok) {S : Nat} (hP : L.P = S + 1) (hc : Ctx L g vv m₀ t) (hr : Ready L t)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hA : CallArgs L W) :
    (privK S).pre (t.callEntry.withRegions (privRd L) (privWr L)) := by
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hs8 := hL.s8192
  have hk := hL.k1024
  have hbS := hL.bS
  rw [hP] at hpQ
  obtain hlow : (⟨L.Q - BitVec.ofNat 64 (S + 1), S + 1⟩ : Region) = L.LOW := by
    show _ = (⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩ : Region); rw [hP]
  obtain sa : ∀ i < 12, stackArg (t.callEntry.withRegions (privRd L) (privWr L)) i = W i := fun i hi => by
    rw [stackArg_ce, hc.sp]; exact R.fr i (by unfold nW frameBytes; omega_arith)
  obtain a0 := (sa 0 (by decide)).trans hA.p
  obtain a1 := (sa 1 (by decide)).trans (hA.args 0 (by decide))
  obtain a2 := (sa 2 (by decide)).trans (hA.args 1 (by decide))
  obtain a3 := (sa 3 (by decide)).trans (hA.args 2 (by decide))
  obtain a4 := (sa 4 (by decide)).trans (hA.args 3 (by decide))
  obtain a5 := (sa 5 (by decide)).trans (hA.args 4 (by decide))
  obtain a6 := (sa 6 (by decide)).trans (hA.args 5 (by decide))
  obtain a7 := (sa 7 (by decide)).trans (hA.args 6 (by decide))
  obtain a8 := (sa 8 (by decide)).trans (hA.args 7 (by decide))
  obtain a9 := (sa 9 (by decide)).trans (hA.args 8 (by decide))
  obtain a10 := (sa 10 (by decide)).trans hA.s10
  obtain a11 := (sa 11 (by decide)).trans hA.s11
  simp only [ourArg] at a1 a2 a3 a4 a5 a6 a7 a8 a9
  obtain aa : stackArgAddr (t.callEntry.withRegions (privRd L) (privWr L)) 0 = L.Q + BitVec.ofNat 64 0 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp]
  obtain arS : Region.Sub ⟨L.Q + BitVec.ofNat 64 0, 96⟩ L.STK := DLay.Ok.sub_stk (by omega_arith)
  obtain lS := DLay.Ok.low_stk (L := L)
  obtain hsl := sl_sub hL
  obtain hOut : Region.Sub ⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩ L.SCR := Offset.sub_base _ (by omega_arith)
  obtain hScr : Region.Sub ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩ L.SCR :=
    Offset.sub_base _ (by rw [hsl]; omega_arith)
  obtain dOS : Region.Disjoint ⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩
      ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩ :=
    Offset.disjoint L.scr (.inl (by omega_arith)) (by omega_arith) (by rw [hsl]; omega_arith)
  simp only [privK, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    hc.sp, gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    hr.x0, hr.x1, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, hr.x7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    aa, hlow, hL.dpl, hL.qil, hL.dql]
  refine ⟨by omega_arith, by omega_arith, trivial, trivial,
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
    (hL.kS.sub_left lS).sub_right hScr, (hL.fr_low (by omega_arith)).symm,
    by rw [BitVec.add_zero]; omega_arith, hL.bR _ (ro_N L), hL.bR _ (ro_E L), hL.bR _ (ro_CT L), hL.bR _ (ro_PP L),
    hL.bR _ (ro_QQ L), hL.bR _ (ro_DP L), hL.bR _ (ro_DQ L), hL.bR _ (ro_QI L),
    by rw [scr8192 hL, hsl]; omega_arith,
    hL.kv, trivial, trivial, hL.el1, hL.elk, hL.pl1, hL.plk, hL.ql1, hL.qlk, trivial, trivial, trivial,
    by rw [hsl]; have := hL.slk; unfold Spec.RsaPss.scratchWords at this; omega_arith⟩

theorem covers_priv (hL : L.Ok) (hc : Ctx L g vv m₀ t) :
    Covers (privRd L ++ privWr L) (t.rd ++ t.wr) ∧ Covers (privWr L) t.wr := by
  obtain z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have hs8 := hL.s8192
  have hk := hL.k1024
  obtain hsl := sl_sub hL
  obtain c1 : ∃ off, L.scr + BitVec.ofNat 64 0 = L.SCR.base + BitVec.ofNat 64 off ∧ off + L.k.toNat ≤ L.SCR.len :=
    ⟨0, rfl, by show 0 + L.k.toNat ≤ L.sl.toNat * 8; omega_arith⟩
  obtain c2 : ∃ off, L.scr + BitVec.ofNat 64 8192 = L.SCR.base + BitVec.ofNat 64 off ∧
      off + (L.sl - BitVec.ofNat 64 1024).toNat * 8 ≤ L.SCR.len :=
    ⟨8192, rfl, by show 8192 + _ ≤ L.sl.toNat * 8; rw [hsl]; omega_arith⟩
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
  obtain hsl := sl_sub hL
  refine WP.callFV v.correct (priv_pre' hL hP hc hr R hA) hcov hcovw
    (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega_arith)
  -- What the call may change: our working space, the rest of `scratch` and the stack below the frame.
  obtain hlow : Region.Sub (below t.sp (16 * v.code.aarch64Depth)) L.LOW := by
    rw [hc.sp]
    show Region.Sub _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
    rw [hP]; exact Offset.sub_below _ hdp (by omega_arith)
  obtain hws : ∀ r ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      Region.Sub r L.SCR ∨ Region.Sub r L.LOW := fun r hr => by
    simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Offset.sub_base _ (by omega_arith))
    · exact .inl (Offset.sub_base _ (by rw [hsl]; omega_arith))
    · exact .inr hlow
  obtain hfr : ∀ d, d + 8 ≤ 424 → (d + 8 ≤ 288 ∨ 288 ≤ d) →
      ∀ X ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)], Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ X :=
    fun d h₁ h₂ X hX => by
      rcases hws X hX with hs | hs
      · rcases h₂ with h₂ | h₂
        · exact hL.stk_buf h₂ (.inr (.inr hs))
        · exact hL.args_buf h₂ h₁ (.inr (.inr hs))
      · exact (hL.fr_low h₁).sub_right hs
  obtain hk' : ∀ d, d + 8 ≤ 424 → (d + 8 ≤ 288 ∨ 288 ≤ d) →
      s'.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (hfr d h₁ h₂) (by decide)
  obtain hc' : Ctx L g vv m₀ s' :=
    ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr h30 => (hcs r hr h30).trans (hc.cs r hr h30),
      fun r hr => (hvs r hr).trans (hc.vs r hr), (hk' 272 (by decide) (by decide)).trans hc.lr,
      fun j hj => (hk' _ (by omega_arith) (by omega_arith)).trans (hc.args j hj), hc.frame.trans (hf.sub fun r hr => by
        rcases hws r hr with hs | hs
        · exact ⟨L.SCR, by simp, hs⟩
        · exact ⟨L.STK, by simp, fun x hx => (DLay.Ok.low_stk (L := L)) x (hs x hx)⟩)⟩
  refine ⟨hc', ⟨fun _ _ => rfl, fun j hj => ?_⟩, ?_⟩
  · have : 8 * j + 8 ≤ 272 := by unfold nW frameBytes at hj; omega_arith
    exact (hk' (8 * j) (by omega_arith) (.inl (by omega_arith))).trans (R.fr j hj)
  obtain sa : ∀ i < 12, stackArg (t.callEntry.withRegions (privRd L) (privWr L)) i = W i := fun i hi => by
    rw [stackArg_ce, hc.sp]; exact R.fr i (by unfold nW frameBytes; omega_arith)
  obtain a0 := (sa 0 (by decide)).trans hA.p
  obtain a1 := (sa 1 (by decide)).trans (hA.args 0 (by decide))
  obtain a2 := (sa 2 (by decide)).trans (hA.args 1 (by decide))
  obtain a3 := (sa 3 (by decide)).trans (hA.args 2 (by decide))
  obtain a4 := (sa 4 (by decide)).trans (hA.args 3 (by decide))
  obtain a6 := (sa 6 (by decide)).trans (hA.args 5 (by decide))
  obtain a8 := (sa 8 (by decide)).trans (hA.args 7 (by decide))
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

end

end

/-!
# RSAES-OAEP decryption on AArch64: correctness

The frames' pushes, the prologue (`prologue_ok`), the private-key operation
(`privW_ok`, `privR_ok`, `priv_call`), its result to its slot and the check
of `k` (`resK_ok`): zeros to `out` and `*msg_len` if `k` is too small
(`decFail_ok`), the decoding otherwise (`decMain_ok`); and the pops:
`dec_ok`, for every implementation of the hash functions and of
`vg_rsa_private_checked`, against the shared contract.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash Stream)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HashTable.AArch64 (tables fnsOf Coh tabOK_of held_tableOf hashAt_tableOf)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Enc.AArch64 (PrivImpl)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (popped_mem popped_sp popped_v popped_gpr_self popped_gpr_ne freed_mem freed_sp
  freed_v freed_gpr add_add)

/-- The private-key operation's result to its slot, zero-extended, and the
check of `k`: `x11` all ones iff `k < 2 hLen + 2`. -/
theorem resK_ok {H : Hash} {u : State} {F S : Addr} (Ly : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hk' : k ≤ 1024) (hD : 2 * H.D + 2 < 65536) :
    WP isa (.block (([.logic .orr .w .x0 .x0 .x0, .addSp .x9 0, .str .x .x0 .x9 sR] : List Instr) ++ chkK H)) u
      fun u' => Lay u' F S ∧ Step F S [] u u' ∧
        Rep u'.mem F S V (upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64)) ∧
        u'.gpr .x11 = if 2 * H.D + 2 ≤ k then 0 else BitVec.allOnes 64 := by
  have G' := Ly.geo
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  have w224 : InRegions u.wr (F + BitVec.ofNat 64 224) 8 := Ly.st (d := 224) (by decide)
  have R1 : Rep (u.mem.write (off F 224) 8 (((u.gpr .x0).setWidth 32).setWidth 64)) F S V
      (upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64)) := R.wq G' (k := 28) (by decide) _
  have rk : (u.mem.write (off F 224) 8 (((u.gpr .x0).setWidth 32).setWidth 64)).read
      (F + BitVec.ofNat 64 168) 8 = BitVec.ofNat 64 k :=
    R1.rd8 (d := 168) (k := 21) rfl (by decide) (by simp only [upd]; exact hk)
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off F 224) 8 (((u.gpr .x0).setWidth 32).setWidth 64) ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x11 = if 2 * H.D + 2 ≤ k then 0 else BitVec.allOnes 64) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11⟩ => ?_
  · oaep_run [chkK, sR, sK, h168, w224, Ly.sp, rk, imm16 hD, sbc_self, BitVec.add_zero, BitVec.or_self]
    refine ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, ?_⟩
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith),
      Nat.mod_eq_of_lt (show 2 * H.D + 2 < 2 ^ 64 by omega_arith)]
  have R' : Rep u'.mem F S V (upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64)) := by rw [hm]; exact R1
  have S' : Step F S [] u u' := ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], by
    rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by decide))⟩
  refine ⟨Ly.congr hsp hwr ?_, S', R', x11⟩
  rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]
  rfl

/-! ## After the prologue -/

/-- What the body leaves: `Ctx`, and `out`, `*msg_len` and the result as
decryption with the private-key operation's outcome says. -/
def Fin (Hs Gs : Spec.Mgf1.Hash) (L : DLay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem)
    (u : State) : Prop :=
  Ctx L g vv m₀ u ∧ Spec.RsaOaep.writtenDecrypt u.mem L.out L.ml L.k.toNat ((u.gpr .x0).setWidth 32)
    (decOut Hs Gs (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat) (privOut L m₀))

/-- The result in its slot and `EM` in our working space, from the call. -/
theorem resD_of {L : DLay} {m₀ : Mem} {u : State} {W : Nat → BitVec 64}
    (hw : Spec.Rsa.writtenOutcome u.mem (L.scr + BitVec.ofNat 64 0) L.k.toNat ((u.gpr .x0).setWidth 32)
      (privOut L m₀)) :
    ResD (fun o => u.mem (off L.scr o)) (upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64)) L.k.toNat
      (privOut L m₀) := by
  have e28 : upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64) 28 = ((u.gpr .x0).setWidth 32).setWidth 64 := by
    simp [upd]
  revert hw
  cases privOut L m₀ with
  | ok em =>
    rintro ⟨hr, hb⟩
    refine ⟨by rw [e28, hr]; rfl, ?_⟩
    rw [← hb]
    refine List.map_congr_left fun i _ => ?_
    show u.mem (L.scr + BitVec.ofNat 64 (0 + i)) = u.mem (L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 i)
    rw [Nat.zero_add, BitVec.add_zero]
  | invalid => rintro ⟨hr, -⟩; show _ = _; rw [e28, hr]; rfl
  | fault => rintro ⟨hr, -⟩; show _ = _; rw [e28, hr]; rfl

theorem resD_len {V : Nat → Byte} {W : Nat → BitVec 64} {k : Nat} {o : Spec.Rsa.Outcome} (h : ResD V W k o) :
    ∀ em, o = .ok em → em.length = k := by
  intro em ho
  subst ho
  rw [← h.2]; simp

variable {Hl : Hash} {Gm : Stream} (hH : StreamOK Hl.stream) (hG : StreamOK Gm) {f : Fns}

theorem decBody_eq (privN : String) (privC : Prog isa) :
    decBody f privN privC = .seq (.block (decPrologue ++ privArgs)) (.seq (.call privN privC)
      (.seq (.block (tabSlot 15)) (.seq (.block lenLoad) (byLen (fun d => decTail (ofLen d) f) lens)))) := rfl

/-- The tail for a digest length, which is all it uses of the hash
function's shape. -/
theorem decTail_D {G G' : Hash} (h : G.D = G'.D) (f : Fns) : decTail G f = decTail G' f := by
  simp only [decTail, decMain, chkK, seedArgs, dbArgs, accLh, scan, tArgs, copyT, decRet, h]

include hH hG in
/-- After the private-key operation, with the frame's words `W` (our
arguments in their slots): the table of the label's hash function to its
slot, its digest length, the check of `k`, and the decoding or the failure. -/
theorem after_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hHm : Hs ∈ Proof.Pbkdf2.Md.AArch64.mdHashes)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) {L : DLay} (hL : L.Ok) (hP16 : 16 ≤ L.P)
    {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {W : Nat → BitVec 64} {u3 : State}
    (hS1 : Slots L W) (hcl : Called L g vv m₀ W u3)
    (okL : Table.TabOK Hl.stream f u3.syms) (hmL : Table.TabMem Hl.stream u3.syms L.tabL m₀)
    (hDL : m₀.readW (L.tabL + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 Hl.stream.D)
    (ok : Table.TabOK Gm f u3.syms) (hm : Table.TabMem Gm u3.syms L.tab m₀)
    (hD : m₀.readW (L.tab + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 Gm.D) :
    WP isa (.seq (.block (tabSlot 15)) (.seq (.block lenLoad) (byLen (fun d => decTail (ofLen d) f) lens))) u3
      (Fin Hs Gs L g vv m₀) := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  have hk64 := hL.k64
  have hk1024 := hL.k1024
  have hDl : Hl.stream.D ∈ lens := by
    show Hl.D ∈ lens
    rw [← hHl]; exact mem_lens hHm
  have Ly3 := hcl.ctx.lay hL hP16 hcl.rep hS1.scr
  -- The table of the label's hash function to its slot, and its digest length to `x16`.
  have TL3 := hcl.ctx.tabL hL hP16 okL hmL hDL
  refine WP.seq (WP.mono (Table.wp_sy (tabSlot_ok (by decide) Ly3 hcl.rep TL3)) fun ua ⟨⟨La, Sa, Ra, x0a⟩, sya⟩ => ?_)
  have TLa := TL3.step Sa sya
  have hDa : ua.mem.readW (L.tabL + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 Hl.stream.D :=
    (TLa.mem _ (Frame.refl _ _)).2.1
  refine WP.seq (WP.mono (Table.wp_sy (lenLoad_ok La Ra (by simp [upd]) TLa.rdD hDa))
    fun ub ⟨⟨Sb, hmb, h16, x0b⟩, syb⟩ => ?_)
  have Lb : Lay ub L.Q L.scr := La.congr Sb.sp Sb.wr (by rw [hmb])
  refine byLen_ok (F := L.Q) (S := L.scr) hDl (by decide) (mem_lens_lt hDl) h16 fun uc Sc hmc syc hgc => ?_
  rw [decTail_D (G := ofLen Hl.stream.D) (G' := Hl) rfl]
  have Lc : Lay uc L.Q L.scr := Lb.congr Sc.sp Sc.wr (by rw [hmc])
  have hmc' : uc.mem = ua.mem := hmc.trans hmb
  have Rc := hmc' ▸ Ra
  have x0c : uc.gpr .x0 = u3.gpr .x0 := ((hgc _ (by decide)).trans x0b).trans x0a
  have Sac := Sa.trans (Sb.trans Sc)
  have syc' : uc.syms = u3.syms := syc.trans (syb.trans sya)
  have hS2 : Slots L (upd W 32 L.tabL) :=
    hS1.of fun j _ h2 _ => by simp only [upd]; rw [ifn (by omega_arith)]
  have hk3 : (upd W 32 L.tabL) 21 = BitVec.ofNat 64 L.k.toNat := by
    rw [hS2.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold decTail Impl.RsaOaep.AArch64.Mgf1.seqs
  refine WP.seq (WP.mono (Table.wp_sy (resK_ok (H := Hl) Lc Rc hk3 hk1024 (by omega_arith)))
    fun u4 ⟨⟨Ly4, S4, R4, x11⟩, sy4⟩ => ?_)
  have hc4 := (hcl.ctx.step hL hP16 Sac fun r h => absurd h List.not_mem_nil).step hL hP16 S4
    fun r h => absurd h List.not_mem_nil
  rw [x0c] at R4
  generalize hW4 : upd (upd W 32 L.tabL) 28
    (((u3.gpr .x0).setWidth 32).setWidth 64) = W4 at R4
  have hres : ResD (fun o => u3.mem (off L.scr o)) W4 L.k.toNat (privOut L m₀) := by
    rw [← hW4]; exact resD_of hcl.out
  have hS4 : Slots L W4 := hW4 ▸ hS2.of fun j _ _ h3 => by simp only [upd]; rw [ifn (by omega_arith)]
  have hk4 : W4 21 = BitVec.ofNat 64 L.k.toNat := by rw [hS4.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h32 : W4 32 = L.tabL := by rw [← hW4]; simp [upd]
  have O4 := hc4.outAt hL hP16 hS4
  have hws : ∀ r ∈ [L.OUT, L.ML], r = L.OUT ∨ r = L.ML := fun r hr => by simpa using hr
  refine WP.ite _ (eval_nonzero u4 .x11) (fun hb => ?_) (fun hb => ?_)
  · -- `k < 2 hLen + 2`: zeros.
    have hkD : L.k.toNat < 2 * Hl.D + 2 := by
      by_contra hc; rw [x11, ifp (by omega_arith)] at hb; exact absurd hb (by decide)
    refine WP.mono (decFail_ok Ly4 R4 O4.ho O4.hml hk4 (by omega_arith) hk1024 O4.hw O4.hnw O4.ha O4.hwm O4.ham O4.hom)
      fun u5 ⟨_, S5, hz5, hm5, hx5⟩ => ⟨hc4.step hL hP16 S5 hws, ?_⟩
    rw [decOut_short (resD_len hres) (by rw [hHl]; exact hkD)]
    have hzs := out_zero (m := u5.mem) (o := L.out) (k := L.k.toNat) hz5
    revert hres
    cases privOut L m₀ with
    | ok em => intro hr; exact ⟨by rw [hx5, fltW, hr.1]; rfl, hzs, hm5⟩
    | invalid => intro hr; exact ⟨by rw [hx5, fltW, show W4 28 = 0 from hr]; rfl, hzs, hm5⟩
    | fault => intro hr; exact ⟨by rw [hx5, fltW, show W4 28 = 2 from hr]; rfl, hzs, hm5⟩
  · -- The decoding.
    have hkD : 2 * Hl.D + 2 ≤ L.k.toNat := by
      by_contra hc; rw [x11, ifn (by omega_arith)] at hb; exact absurd hb (by decide)
    have sy : u4.syms = u3.syms := sy4.trans syc'
    have T4 := hc4.tab hL hP16 (sy ▸ ok) (sy ▸ hm) hD
    have TL4 := hc4.tabL hL hP16 (sy ▸ okL) (sy ▸ hmL) hDL
    refine WP.mono (decMain_ok hH hG hHh hHl hHv hGh hGl hGv TL4 T4 Ly4 R4 h32 hk4 hkD hk1024
      (hc4.labAt hL hP16 hS4) O4 hres)
      fun u5 ⟨_, S5, hw5⟩ => ⟨hc4.step hL hP16 S5 hws, ?_⟩
    have hlab := hc4.bytes_ro hL (ro_LAB L)
    simp only at hlab
    rw [hlab] at hw5
    exact hw5

include hH hG in
theorem rest_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hHm : Hs ∈ Proof.Pbkdf2.Md.AArch64.mdHashes)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (pv : PrivImpl) {L : DLay} (hL : L.Ok) (hP : L.P = pv.S + 1)
    {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State} (hc : Ctx L g vv m₀ t)
    (h9 : t.gpr .x9 = L.Q) (hpw : Prologued L (fun j => word t.mem L.Q (8 * j)))
    (okL : Table.TabOK Hl.stream f t.syms) (hmL : Table.TabMem Hl.stream t.syms L.tabL m₀)
    (hDL : m₀.readW (L.tabL + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 Hl.stream.D)
    (ok : Table.TabOK Gm f t.syms) (hm : Table.TabMem Gm t.syms L.tab m₀)
    (hD : m₀.readW (L.tab + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 Gm.D) :
    WP isa (.block privArgs) t fun u => WP isa (.seq (.call pv.name pv.code)
      (.seq (.block (tabSlot 15)) (.seq (.block lenLoad) (byLen (fun d => decTail (ofLen d) f) lens)))) u
        (Fin Hs Gs L g vv m₀) := by
  have hS15 := pv.S15
  have hP16 : 16 ≤ L.P := by omega_arith
  rw [privArgs_eq, WP.block_append_iff]
  have R₀ : Rep t.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (fun j => word t.mem L.Q (8 * j)) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  refine WP.mono (Table.wp_sy (privW_ok hL hP16 hc h9 R₀ hpw.slots)) fun u1 ⟨⟨hc1, _, R1⟩, sy1⟩ => ?_
  have hS1 : Slots L (privW L fun j => word t.mem L.Q (8 * j)) :=
    hpw.slots.of fun j _ _ h3 => by simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]
  refine WP.mono (Table.wp_sy (privR_ok hL hP16 hc1 R1 hS1)) fun u2 ⟨⟨hc2, hm2, hr2⟩, sy2⟩ => ?_
  have R2 : Rep u2.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (privW L fun j => word t.mem L.Q (8 * j)) :=
    hm2 ▸ R1
  have hA : CallArgs L (privW L fun j => word t.mem L.Q (8 * j)) :=
    ⟨by simp only [privW, upd]; exact hpw.p, fun j hj => by
      simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]; exact hpw.args j hj,
      by simp [privW, upd], by simp [privW, upd]⟩
  refine WP.seq (WP.mono (Table.wp_sy (priv_call pv hL hP hc2 hr2 R2 hA)) fun u3 ⟨hcl, sy3⟩ => ?_)
  have sy03 : u3.syms = t.syms := sy3.trans (sy2.trans sy1)
  exact after_ok hH hG hHh hHl hHv hHm hGh hGl hGv hL hP16 hS1 hcl (sy03 ▸ okL) (sy03 ▸ hmL) hDL (sy03 ▸ ok)
    (sy03 ▸ hm) hD

/-! ## The whole function -/

/-- The stack the contract gives. -/
theorem spec_sp {ts : List FnTable} {P : Nat} {s : State} (h : (decSpec ts P).pre s) :
    P + 288 ≤ s.sp.toNat := by
  dec_pre at h
  exact h.1

/-- `writtenDecrypt` reads the memory only in the output and its length. -/
theorem writtenDecrypt_congr {m m' : Mem} {out len : Addr} {k : Nat} {r : BitVec 32}
    {o} (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k)
    (hl : m'.readW len 64 = m.readW len 64) (h : Spec.RsaOaep.writtenDecrypt m out len k r o) :
    Spec.RsaOaep.writtenDecrypt m' out len k r o := by
  cases o <;> simp only [Spec.RsaOaep.writtenDecrypt, hb, hl] at h ⊢ <;> exact h

/-- The postcondition, from what the body wrote with `Hs` and `Gs`, the hash
functions the tables name. -/
theorem result_ok {Hs Gs : Spec.Mgf1.Hash} {ts : List FnTable} {P : Nat} {s : State} {t : State}
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some Hs)
    (hG : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some Gs)
    (hw : Spec.RsaOaep.writtenDecrypt t.mem (lay P s).out (lay P s).ml (lay P s).k.toNat ((t.gpr .x0).setWidth 32)
      (decOut Hs Gs (Spec.Rsa.bytesAt s.mem (lay P s).lab (lay P s).labl.toNat) (privOut (lay P s) s.mem))) :
    (decSpec ts P).post s t := by
  sig_post [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  intro H' G' hH' hG'
  obtain rfl : Hs = H' := Option.some.inj (hH.symm.trans hH')
  obtain rfl : Gs = G' := Option.some.inj (hG.symm.trans hG')
  rw [decrypt_eq (by simp [Spec.Rsa.bytesAt])]
  exact hw

/-- `vg_rsa_oaep_decrypt` meets the shared contract and the calling
convention, with both hash functions the tables of `vs`. -/
theorem dec_ok {vs : List MdHash} (hc : Coh vs) (pv : PrivImpl) {s : State}
    (h : (decSpec (tables vs) (pv.S + 1)).pre s) :
    WP isa (decrypt (fnsOf vs) pv.name pv.code) s fun s' =>
      abiPreserved s s' ∧ (decSpec (tables vs) (pv.S + 1)).post s s' := by
  have hL := lay_ok h
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hS := pv.S15
  have hsp := spec_sp h
  obtain ⟨⟨T₁, hT₁, hheld₁⟩, ⟨T, hT, hheld⟩, hpw⟩ := spec_tab h
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨hmL, hixL, hDL⟩ := held_tableOf hheld₁
  obtain ⟨hm, hix, hD⟩ := held_tableOf hheld
  have okL := tabOK_of hc hpw hw₁
  have ok := tabOK_of hc hpw hw
  have hHa := hashAt_tableOf hixL
  have hGa := hashAt_tableOf hix
  refine WP.frameAlloc (by omega_arith) (by decide) ?_ ?_
  · show 272 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_arith)]
    show 272 ≤ s.sp.toNat - 16
    omega_arith
  · show WP isa (decBody (fnsOf vs) pv.name pv.code) (entered s) _
    rw [decBody_eq]
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (Table.wp_sy (prologue_ok h)) fun t ⟨⟨hc, h9, hpw⟩, sy⟩ => ?_
    have sy' : t.syms = s.syms := sy
    refine WP.mono (rest_ok w₁.ok.stream w.ok.stream w₁.mgf.hash w₁.mgf.len (mgf_valid w₁.mgf) w₁.mgf.mem
      w.mgf.hash w.mgf.len (mgf_valid w.mgf) pv hL rfl hc h9 hpw (sy' ▸ okL) (sy' ▸ hmL) hDL
      (sy' ▸ ok) (sy' ▸ hm) hD) fun u hu => ?_
    refine WP.mono hu fun u' ⟨hc', hw'⟩ mm uu fl => ?_
    have hsp' : (freed frameBytes u').sp = (lay (pv.S + 1) s).Q + BitVec.ofNat 64 272 := by
      rw [freed_sp, hc'.sp]; rfl
    -- The output and its length lie apart from the stack, whose frames' bytes are lost.
    obtain hS : Region.Sub (below s.sp (272 + 16)) (lay (pv.S + 1) s).STK := by
      obtain h288 := DLay.Ok.sub_stk (L := lay (pv.S + 1) s) (d := 0) (n := 288) (by omega_arith)
      rw [show (lay (pv.S + 1) s).Q + BitVec.ofNat 64 0 = (lay (pv.S + 1) s).Q from BitVec.add_zero _] at h288
      exact h288
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
    · show (popped .x30 (freed frameBytes u')).gpr r = s.gpr r
      by_cases h30 : r = .x30
      · subst r
        rw [popped_gpr_self, freed_mem, hsp']; exact hc'.lr
      · rw [popped_gpr_ne _ h30, freed_gpr]
        exact hc'.cs r hr h30
    · show (popped .x30 (freed frameBytes u')).sp = s.sp
      rw [popped_sp, hsp']
      show (lay (pv.S + 1) s).Q + BitVec.ofNat 64 272 + BitVec.ofNat 64 16 = s.sp
      rw [add_add]; exact lay_Q _ s
    · exact hc'.vs r hr
    · refine result_ok hHa hGa (writtenDecrypt_congr (m := u'.mem)
        (List.map_congr_left fun i hi => lost_byte fl (hL.kO.symm.sub_right hS) (List.mem_range.mp hi))
        (fl.readW (r := (lay (pv.S + 1) s).ML) (Region.contains_self _ _) (fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR; exact hL.kM.symm.sub_right hS) (by decide)) ?_)
      show Spec.RsaOaep.writtenDecrypt u'.mem _ _ _ (((popped .x30 (freed frameBytes u')).gpr .x0).setWidth 32) _
      rw [popped_gpr_ne _ (by decide), freed_gpr]
      exact hw'

end VG.Proof.RsaOaep.AArch64.Dec
