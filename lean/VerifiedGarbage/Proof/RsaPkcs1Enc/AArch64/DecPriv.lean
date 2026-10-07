import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecEntry
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: the private-key operation

Once `setup` has run (`Ready`), `priv_pre'` is the precondition of
`vg_rsa_private_checked` on the call's entry, which it is given `n`, `e`,
the input, the key's factors and its stack arguments (the frame's first 96
bytes) to read and `out` and `scratch` to write; and `priv_call` runs it:
`Ctx` holds again, and `out` holds `EM` (or zeros) as `privOut` says.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce bytesAt_eq)

theorem ro_N (L : Lay) : L.N ∈ L.ro := List.mem_cons_self ..
theorem ro_E (L : Lay) : L.E ∈ L.ro := List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem ro_D (L : Lay) : L.D ∈ L.ro := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem ro_INP (L : Lay) : L.INP ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
theorem ro_PP (L : Lay) : L.PP ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..))))
theorem ro_QQ (L : Lay) : L.QQ ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
theorem ro_DP (L : Lay) : L.DP ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
theorem ro_DQ (L : Lay) : L.DQ ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
theorem ro_QI (L : Lay) : L.QI ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))))))

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
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

/-- The regions the call reads and writes. -/
abbrev privRd (L : Lay) : List Region :=
  [L.N, L.E, L.INP, L.PP, L.QQ, L.DP, L.DQ, L.QI, ⟨L.Q + BitVec.ofNat 64 0, 96⟩]
abbrev privWr (L : Lay) : List Region := [L.OUT, L.SCR]

/-- What the private-key operation gives, from the buffers on entry. -/
def privOut (L : Lay) (m₀ : Mem) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
    (Spec.Rsa.bytesAt m₀ L.inp L.k.toNat) (Spec.Rsa.bytesAt m₀ L.p L.pl.toNat)
    (Spec.Rsa.bytesAt m₀ L.q L.ql.toNat) (Spec.Rsa.bytesAt m₀ L.dp L.pl.toNat)
    (Spec.Rsa.bytesAt m₀ L.dq L.ql.toNat) (Spec.Rsa.bytesAt m₀ L.qi L.pl.toNat)

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- The call's stack arguments are the frame's first twelve words. -/
theorem priv_args (hc : Ctx L g vv m₀ t) (rd wr : List Region) :
    stackArg (t.callEntry.withRegions rd wr) 0 = L.p ∧ stackArg (t.callEntry.withRegions rd wr) 1 = L.pl ∧
    stackArg (t.callEntry.withRegions rd wr) 2 = L.q ∧ stackArg (t.callEntry.withRegions rd wr) 3 = L.ql ∧
    stackArg (t.callEntry.withRegions rd wr) 4 = L.dp ∧ stackArg (t.callEntry.withRegions rd wr) 5 = L.dpl ∧
    stackArg (t.callEntry.withRegions rd wr) 6 = L.dq ∧ stackArg (t.callEntry.withRegions rd wr) 7 = L.dql ∧
    stackArg (t.callEntry.withRegions rd wr) 8 = L.qi ∧ stackArg (t.callEntry.withRegions rd wr) 9 = L.qil ∧
    stackArg (t.callEntry.withRegions rd wr) 10 = L.scr ∧ stackArg (t.callEntry.withRegions rd wr) 11 = L.sl := by
  simp only [stackArg_ce, hc.sp]
  exact ⟨hc.kept.call 0 (by decide), hc.kept.call 1 (by decide), hc.kept.call 2 (by decide),
    hc.kept.call 3 (by decide), hc.kept.call 4 (by decide), hc.kept.call 5 (by decide),
    hc.kept.call 6 (by decide), hc.kept.call 7 (by decide), hc.kept.call 8 (by decide),
    hc.kept.call 9 (by decide), hc.kept.call 10 (by decide), hc.kept.call 11 (by decide)⟩

theorem priv_pre' (hL : L.Ok) {S : Nat} (hP : L.P = S + 1) (hc : Ctx L g vv m₀ t) (hr : Ready L t) :
    (privK S).pre (t.callEntry.withRegions (privRd L) (privWr L)) := by
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  rw [hP] at hpQ
  have hlow : (⟨L.Q - BitVec.ofNat 64 (S + 1), S + 1⟩ : Region) = L.LOW := by
    show _ = (⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩ : Region); rw [hP]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := priv_args hc (privRd L) (privWr L)
  have aa : stackArgAddr (t.callEntry.withRegions (privRd L) (privWr L)) 0 = L.Q + BitVec.ofNat 64 0 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp]
  have arS : Region.Sub ⟨L.Q + BitVec.ofNat 64 0, 96⟩ L.STK := Lay.Ok.sub_stk (by omega)
  have lS := Lay.Ok.low_stk (L := L)
  simp only [privK, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    hc.sp, gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    hr.x0, hr.x1, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, hr.x7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    aa, hlow, hL.dpl, hL.qil, hL.dql]
  refine ⟨by omega, by omega, trivial, trivial,
    hL.oR _ (ro_N L), hL.oR _ (ro_E L), hL.oR _ (ro_INP L), hL.oR _ (ro_PP L), hL.oR _ (ro_QQ L),
    hL.oR _ (ro_DP L), hL.oR _ (ro_DQ L), hL.oR _ (ro_QI L), hL.oS, (hL.kO.sub_left arS).symm,
    (hL.sR _ (ro_N L)).symm, (hL.sR _ (ro_E L)).symm, (hL.sR _ (ro_INP L)).symm, (hL.sR _ (ro_PP L)).symm,
    (hL.sR _ (ro_QQ L)).symm, (hL.sR _ (ro_DP L)).symm, (hL.sR _ (ro_DQ L)).symm, (hL.sR _ (ro_QI L)).symm,
    (hL.kS.sub_left arS).symm,
    hL.kO.sub_left lS, (hL.kR _ (ro_N L)).sub_left lS, (hL.kR _ (ro_E L)).sub_left lS,
    (hL.kR _ (ro_INP L)).sub_left lS, (hL.kR _ (ro_PP L)).sub_left lS, (hL.kR _ (ro_QQ L)).sub_left lS,
    (hL.kR _ (ro_DP L)).sub_left lS, (hL.kR _ (ro_DQ L)).sub_left lS, (hL.kR _ (ro_QI L)).sub_left lS,
    hL.kS.sub_left lS, (hL.fr_low (by omega)).symm,
    hL.bO, hL.bR _ (ro_N L), hL.bR _ (ro_E L), hL.bR _ (ro_INP L), hL.bR _ (ro_PP L), hL.bR _ (ro_QQ L),
    hL.bR _ (ro_DP L), hL.bR _ (ro_DQ L), hL.bR _ (ro_QI L), hL.bS,
    hL.kv, trivial, trivial, hL.el1, hL.elk, hL.pl1, hL.plk, hL.ql1, hL.qlk, trivial, trivial, trivial, hL.slk⟩

theorem covers_priv (hc : Ctx L g vv m₀ t) :
    Covers (privRd L ++ privWr L) (t.rd ++ t.wr) ∧ Covers (privWr L) t.wr := by
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  rw [hc.rd, hc.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [privRd, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.N, by simp, 0, z _, by simp⟩
    · exact ⟨L.E, by simp, 0, z _, by simp⟩
    · exact ⟨L.INP, by simp, 0, z _, by simp⟩
    · exact ⟨L.PP, by simp, 0, z _, by simp⟩
    · exact ⟨L.QQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.DP, by simp, 0, z _, by simp⟩
    · exact ⟨L.DQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.QI, by simp, 0, z _, by simp⟩
    · exact ⟨L.FR, by simp, 0, rfl, by show 0 + 96 ≤ frameBytes; decide⟩
    · exact ⟨L.OUT, by simp, 0, z _, by simp⟩
    · exact ⟨L.SCR, by simp, 0, z _, by simp⟩
  · simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, 0, z _, by simp⟩
    · exact ⟨L.SCR, by simp, 0, z _, by simp⟩

/-- After the call. -/
structure Called (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t' : State) : Prop where
  ctx : Ctx L g vv m₀ t'
  out : Spec.Rsa.writtenOutcome t'.mem L.out L.k.toNat ((t'.gpr .x0).setWidth 32) (privOut L m₀)

theorem priv_call (v : PrivImpl) (hL : L.Ok) (hP : L.P = v.S + 1) (hc : Ctx L g vv m₀ t) (hr : Ready L t) :
    WP isa (.call v.name v.code) t (Called L g vv m₀) := by
  have hnQ := hL.nQ
  have hdp := v.depth'
  have hpQ := hL.pQ
  rw [hP] at hpQ
  obtain ⟨hcov, hcovw⟩ := covers_priv hc
  refine WP.callFV v.correct (priv_pre' hL hP hc hr) hcov hcovw
    (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  -- What the call may change: `out`, `scratch` and the stack below the frame.
  have hlow : Region.Sub (below t.sp (16 * v.code.aarch64Depth)) L.LOW := by
    rw [hc.sp]
    show Region.Sub _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
    rw [hP]; exact Offset.sub_below _ hdp (by omega)
  have hws : ∀ r ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      (Region.Sub r L.OUT ∨ Region.Sub r L.SCR) ∨ Region.Sub r L.LOW := fun r hr => by
    simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (.inl fun _ h => h)
    · exact .inl (.inr fun _ h => h)
    · exact .inr hlow
  have hkept : ∀ d, keptOff d → ∀ R ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R := fun d hd R hR => by
    rcases hws R hR with (hs | hs) | hs
    · exact hL.kept_buf hd (.inl hs)
    · exact hL.kept_buf hd (.inr (.inr hs))
    · exact (hL.fr_low (by unfold keptOff at hd; omega)).sub_right hs
  have hc' : Ctx L g vv m₀ s' :=
    ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr h30 => (hcs r hr h30).trans (hc.cs r hr h30),
      fun r hr => (hvs r hr).trans (hc.vs r hr), hc.kept.frame hf hkept, hc.frame.trans (hf.sub fun r hr => by
        rcases hws r hr with (hs | hs) | hs
        · exact ⟨L.OUT, by simp, hs⟩
        · exact ⟨L.SCR, by simp, hs⟩
        · exact ⟨L.STK, by simp, fun x hx => (Lay.Ok.low_stk (L := L)) x (hs x hx)⟩)⟩
  refine ⟨hc', ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, -, -, -⟩ := priv_args hc (privRd L) (privWr L)
  have hp := hpost
  simp only [privK, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs),
    hr.x0, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, a0, a1, a2, a3, a4, a6, a8] at hp
  rw [hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_E L), hc.bytes_ro hL (ro_INP L), hc.bytes_ro hL (ro_PP L),
    hc.bytes_ro hL (ro_QQ L), hc.bytes_ro hL (ro_DP L), hc.bytes_ro hL (ro_DQ L), hc.bytes_ro hL (ro_QI L)] at hp
  exact hp

end

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
