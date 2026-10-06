import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLoops

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: the call

Once `PS` and `M` are copied, the frame holds
`EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` (`em_bytes`). `callArgs` sets the call's
`input` and `input_len` (`CallReady`); `pub_pre'` is the precondition of
`vg_rsa_public_checked` on the call's entry, which it is given `n`, `e`, `EM`
and its stack arguments to read and `out` and `scratch` to write; and
`pub_call` runs it (`call_ok`): `Ctx` holds again, and `out` holds
`EM^e mod n` or zeros.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, add_add]

/-- The bytes at `p`, each given. -/
theorem bytesAt_eq {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = m' (q + BitVec.ofNat 64 i)) :
    Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt m' q n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The encoded message in the frame. -/
theorem em_bytes {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : MsgInv L g vv m₀ L.ml.toNat t) :
    Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM) L.k.toNat =
      Spec.RsaPkcs1Enc.encode (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat) := by
  rw [← hL.em_len, show L.pl.toNat + L.ml.toNat + 3 = ((2 + L.pl.toNat) + 1) + L.ml.toNat by omega,
    bytesAt_add, bytesAt_add, bytesAt_add, Spec.RsaPkcs1Enc.encode]
  have e2 : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM) 2 = [0x00, 0x02] := by
    simp only [Spec.Rsa.bytesAt, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, add_add, Nat.add_zero, h.b0, h.b1]
  have eP : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM + BitVec.ofNat 64 2) L.pl.toNat =
      Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat :=
    bytesAt_eq fun i hi => by rw [add_add, add_add, ← Nat.add_assoc]; exact h.ps i hi
  have eS : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM + BitVec.ofNat 64 (2 + L.pl.toNat)) 1 = [0x00] := by
    simp only [Spec.Rsa.bytesAt, List.range_one, List.map_cons, List.map_nil, add_add, Nat.add_zero, ← Nat.add_assoc,
      h.sep]
  have eM : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM + BitVec.ofNat 64 (2 + L.pl.toNat + 1)) L.ml.toNat =
      Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat :=
    bytesAt_eq fun i hi => by
      rw [add_add, add_add, show oEM + (2 + L.pl.toNat + 1 + i) = oEM + 3 + L.pl.toNat + i by omega]
      exact h.msg i hi
  rw [e2, eP, eS, eM]

/-- The regions the call reads and writes. -/
abbrev pubRd (L : Lay) : List Region := [L.N, L.E, L.EM, ⟨L.Q + BitVec.ofNat 64 0, 16⟩]
abbrev pubWr (L : Lay) : List Region := [⟨L.out, L.ol.toNat⟩, L.SCR]

/-- Before the call. -/
structure CallReady (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  x0 : t.gpr .x0 = L.out
  x1 : t.gpr .x1 = L.ol
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.Q + BitVec.ofNat 64 oEM
  x7 : t.gpr .x7 = L.k
  em : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM) L.k.toNat =
    Spec.RsaPkcs1Enc.encode (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)
  z : t.mem.readW (L.Q + BitVec.ofNat 64 oZ) 64 = zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)

/-- The registers on entry are the layout's. -/
def RegsOf (L : Lay) (g : Reg → BitVec 64) : Prop :=
  g .x0 = L.out ∧ g .x1 = L.ol ∧ g .x2 = L.n ∧ g .x3 = L.k ∧ g .x4 = L.e ∧ g .x5 = L.el ∧ g .x6 = L.msg ∧
    g .x7 = L.ml

theorem callArgs_inv {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hg : RegsOf L g) (h : MsgInv L g vv m₀ L.ml.toNat t) :
    WP isa (.block callArgs) t (CallReady L g vv m₀) :=
  WP.mono (callArgs_ok t) fun w hw => by
    have go : ∀ r, r ≠ .x6 → r ≠ .x7 → w.gpr r = t.gpr r := hw.other
    refine ⟨h.ctx.regs hw.rd hw.wr hw.sp hw.mem hw.v fun r hr _ => go r (mem_ne hr (by decide))
      (mem_ne hr (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [go .x0 (by decide) (by decide), h.x0, hg.1]
    · rw [go .x1 (by decide) (by decide), h.x1, hg.2.1]
    · rw [go .x2 (by decide) (by decide), h.x2, hg.2.2.1]
    · rw [go .x3 (by decide) (by decide), h.x3, hg.2.2.2.1]
    · rw [go .x4 (by decide) (by decide), h.x4, hg.2.2.2.2.1]
    · rw [go .x5 (by decide) (by decide), h.x5, hg.2.2.2.2.2.1]
    · rw [hw.x6, h.ctx.sp]
    · rw [hw.x7, h.x3, hg.2.2.2.1]
    · rw [hw.mem]; exact em_bytes hL h
    · rw [hw.mem]; exact h.z

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem stackArg_ce (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (t.sp + BitVec.ofNat 64 (8 * i)) 64 := rfl

theorem pub_pre' {L : Lay} (hL : L.Ok) {S : Nat} (hP : L.P = S + 1) {g : Reg → BitVec 64}
    {vv : VReg → BitVec 128} {m₀ : Mem} {t : State} (h : CallReady L g vv m₀ t) :
    (pubK S).pre (t.callEntry.withRegions (pubRd L) (pubWr L)) := by
  have hc := h.ctx
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hk := hL.k1024
  have olk := hL.olk
  rw [hP] at hpQ
  have hlow : (⟨L.Q - BitVec.ofNat 64 (S + 1), S + 1⟩ : Region) = L.LOW := by
    show _ = (⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩ : Region); rw [hP]
  have hQ40 : (L.Q + BitVec.ofNat 64 oEM).toNat = L.Q.toNat + oEM := by
    rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by unfold oEM; omega), Nat.mod_eq_of_lt (by unfold oEM; omega)]
  -- The call's stack arguments are the frame's first two words.
  have a0 : stackArg (t.callEntry.withRegions (pubRd L) (pubWr L)) 0 = L.scr := by
    rw [stackArg_ce, hc.sp]; exact hc.kept.scr
  have a1 : stackArg (t.callEntry.withRegions (pubRd L) (pubWr L)) 1 = L.sl := by
    rw [stackArg_ce, hc.sp]; exact hc.kept.sl
  have aa : stackArgAddr (t.callEntry.withRegions (pubRd L) (pubWr L)) 0 = L.Q + BitVec.ofNat 64 0 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp]
  have emS : Region.Sub L.EM L.STK := Lay.Ok.sub_stk (by unfold oEM; omega)
  have arS : Region.Sub ⟨L.Q + BitVec.ofNat 64 0, 16⟩ L.STK := Lay.Ok.sub_stk (by omega)
  simp only [pubK, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    hc.sp, gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, a0, a1, aa, hlow, olk]
  refine ⟨by omega, by omega, trivial, by rw [pubWr, olk], hL.oN, hL.oE, hL.kO.symm.sub_right emS, hL.oS,
    hL.kO.symm.sub_right arS, hL.nS, hL.eS, hL.kS.sub_left emS,
    (hL.kS.sub_left arS).symm, ?_, ?_, ?_, ?_, ?_, ?_, hL.bO, hL.bN, hL.bE, by rw [hQ40]; unfold oEM; omega,
    hL.bS, hL.kv, trivial, trivial, hL.el1, hL.elk, hL.slk⟩
  · exact hL.kO.sub_left (Lay.Ok.low_stk (L := L))
  · exact hL.kN.sub_left (Lay.Ok.low_stk (L := L))
  · exact hL.kE.sub_left (Lay.Ok.low_stk (L := L))
  · exact (hL.fr_low (by unfold oEM; omega)).symm
  · exact hL.kS.sub_left (Lay.Ok.low_stk (L := L))
  · exact (hL.fr_low (by omega)).symm

theorem covers_pub {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) :
    Covers (pubRd L ++ pubWr L) (t.rd ++ t.wr) ∧ Covers (pubWr L) t.wr := by
  have hk := hL.k1024
  have olk := hL.olk
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  rw [hc.rd, hc.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [pubRd, pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.N, by simp, 0, z _, by simp⟩
    · exact ⟨L.E, by simp, 0, z _, by simp⟩
    · exact ⟨L.FR, by simp, oEM, rfl, by show oEM + L.k.toNat ≤ frameBytes; unfold oEM frameBytes; omega⟩
    · exact ⟨L.FR, by simp, 0, rfl, by show 0 + 16 ≤ frameBytes; decide⟩
    · exact ⟨L.OUT, by simp, 0, z _, by simp [olk]⟩
    · exact ⟨L.SCR, by simp, 0, z _, by simp⟩
  · simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, 0, z _, by simp [olk]⟩
    · exact ⟨L.SCR, by simp, 0, z _, by simp⟩

/-- After the call. -/
structure Called (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t' : State) : Prop where
  ctx : Ctx L g vv m₀ t'
  z : t'.mem.readW (L.Q + BitVec.ofNat 64 oZ) 64 = zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)
  out : Spec.Rsa.written t'.mem L.out L.k.toNat ((t'.gpr .x0).setWidth 32)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
      (Spec.RsaPkcs1Enc.encode (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)))

theorem pub_call (v : PubImpl) {L : Lay} (hL : L.Ok) (hP : L.P = v.S + 1) {g : Reg → BitVec 64}
    {vv : VReg → BitVec 128} {m₀ : Mem} {t : State} (h : CallReady L g vv m₀ t) :
    WP isa (.call v.name v.code) t (Called L g vv m₀) := by
  have hc := h.ctx
  have hnQ := hL.nQ
  have hk := hL.k1024
  have hdp := v.depth'
  have hpQ := hL.pQ
  rw [hP] at hpQ
  obtain ⟨hcov, hcovw⟩ := covers_pub hL hc
  refine WP.callFV v.correct (pub_pre' hL hP h) hcov hcovw
    (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  -- What the call may change: `out`, `scratch` and the stack below the frame.
  have hlow : Region.Sub (below t.sp (16 * v.code.aarch64Depth)) L.LOW := by
    rw [hc.sp]
    show Region.Sub _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
    rw [hP]; exact Offset.sub_below _ hdp (by omega)
  have hws : ∀ r ∈ pubWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      (Region.Sub r L.OUT ∨ Region.Sub r L.SCR) ∨ Region.Sub r L.LOW := fun r hr => by
    simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (.inl (Region.sub_prefix (by rw [hL.olk])))
    · exact .inl (.inr fun _ h => h)
    · exact .inr hlow
  have hkept : ∀ d, keptOff d → ∀ R ∈ pubWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R := fun d hd R hR => by
    rcases hws R hR with hs | hs
    · exact hL.kept_buf hd hs
    · exact (hL.fr_low (by unfold keptOff at hd; omega)).sub_right hs
  have hzr : ∀ R ∈ pubWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      Region.Disjoint ⟨L.Q + BitVec.ofNat 64 oZ, 8⟩ R := fun R hR => by
    rcases hws R hR with hs | hs
    · rcases hs with hs | hs
      · exact (hL.stk_buf (by decide) (.inl rfl)).sub_right hs
      · exact (hL.stk_buf (by decide) (.inr (.inr (.inr (.inr (.inr rfl)))))).sub_right hs
    · exact (hL.fr_low (by decide)).sub_right hs
  refine ⟨⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr h30 => (hcs r hr h30).trans (hc.cs r hr h30),
    fun r hr => (hvs r hr).trans (hc.vs r hr), hc.kept.frame hf hkept, hc.frame.trans (hf.sub fun r hr => ?_)⟩,
    ?_, ?_⟩
  · rcases hws r hr with (hs | hs) | hs
    · exact ⟨L.OUT, by simp, hs⟩
    · exact ⟨L.SCR, by simp, hs⟩
    · exact ⟨L.STK, by simp, fun x hx => (Lay.Ok.low_stk (L := L)) x (hs x hx)⟩
  · rw [hf.readW (Region.contains_self _ _) hzr (by decide)]; exact h.z
  · have hp := hpost
    simp only [pubK, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs),
      h.x0, h.x2, h.x3, h.x4, h.x5, h.x6, h.em] at hp
    rw [bytesAt_eq (n := L.k.toNat) (fun i hi => hc.byte_ro (R := L.N) hL.oN.symm hL.nS hL.kN.symm
        (Nat.le_of_lt L.k.isLt) hi),
      bytesAt_eq (n := L.el.toNat) (fun i hi => hc.byte_ro (R := L.E) hL.oE.symm hL.eS hL.kE.symm
        (Nat.le_of_lt L.el.isLt) hi)] at hp
    exact hp

end VG.Proof.RsaPkcs1Enc.AArch64.Enc
