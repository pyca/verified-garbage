import VerifiedGarbage.Proof.RsaPss.X86_64.SignFail

/-!
# RSASSA-PSS signing on x86-64: the call of `vg_rsa_private_checked`

With its stack arguments in the frame's first 14 words (`EM` at
`scratch + oEm` as the input, the private key, the rest of `scratch`),
`vg_rsa_private_checked` runs under its contract (`priv_pre`), and returns
with `out` written as it says, the frame and our working space kept
(`priv_call`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)

variable {G : Spec.Mgf1.Hash}

/-- `out`, and the caller's working space. -/
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩

/-- What the private-key operation reads: `n`, `e`, `EM`, the private key and
its stack arguments. -/
def pRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨off (stackArg s 13) oEm, (s.gpr .rcx).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩,
    ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨fb s, 112⟩]

/-- What it writes: `out`, and the rest of the working space. -/
def pWr (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩,
    ⟨off (stackArg s 13) oRsa, (stackArg s 14 - BitVec.ofNat 64 1024).toNat * 8⟩]

/-- Its stack arguments. -/
def pArg (s : State) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => off (stackArg s 13) oEm
  | 1 => s.gpr .rcx
  | 12 => off (stackArg s 13) oRsa
  | 13 => stackArg s 14 - BitVec.ofNat 64 1024
  | i => stackArg s (i - 2)

theorem fb_sub8' {s : State} (hp : SPre G s) : (fb s - 8).toNat = (fb s).toNat - 8 := by
  have hF := fb_toNat hp; have := hp.sp1
  rw [BitVec.toNat_sub]; unfold signStack Proof.Rsa.X86_64.stackBytes frameBytes at *
  rw [show (8 : BitVec 64).toNat = 8 from rfl]; omega

/-- A stack argument of a function called from the frame is a word of it. -/
theorem stackArg_call {s t : State} (hp : SPre G s) (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat}
    (hi : i < 14) : stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hF := fb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hsep := Offset.sep (fb s - 8) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega) (by omega)
    (by omega)
  rw [show fb s - 8 + BitVec.ofNat 64 0 = fb s - 8 from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  have ea : fb s - 8 + BitVec.ofNat 64 (8 * (i + 1)) = off (fb s) (8 * i) := by
    simp only [off]
    rw [show 8 * (i + 1) = 8 + 8 * i by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      show BitVec.ofNat 64 8 = 8 from rfl, BitVec.sub_add_cancel]
  rw [ea]

theorem stackArgAddr_call {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp]
  exact BitVec.sub_add_cancel _ _

theorem priv_pre {s t : State} (hp : SPre G s) (hsp : t.gpr .rsp = fb s)
    (hargs : ∀ i < 14, word t.mem (fb s) (8 * i) = pArg s i) (hdi : t.gpr .rdi = s.gpr .rdi)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    chkContract.pre (t.callEntry.withRegions (pRd s) (pWr s)) := by
  have hE : ∀ i < 14, stackArg (t.callEntry.withRegions (pRd s) (pWr s)) i = pArg s i :=
    fun i hi => (stackArg_call hp hsp _ _ hi).trans (hargs i hi)
  simp only [chkContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hsp, stackArgAddr_call hsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), hE 4 (by decide), hE 5 (by decide), hE 6 (by decide), hE 7 (by decide),
    hE 8 (by decide), hE 9 (by decide), hE 10 (by decide), hE 11 (by decide), hE 12 (by decide), hE 13 (by decide),
    pArg, Nat.reduceSub]
  have hF := fb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hk1 := hp.k1; have hk2 := hp.k2
  have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hss : signStack = 3648 := rfl
  have hsb : Rsa.X86_64.stackBytes = 3248 := rfl
  have c1 : oEm = 2560 := rfl
  have c2 : oRsa = 8192 := rfl
  have hsi := hp.hsi
  have h8 := fb_sub8' hp
  have hsc : (stackArg s 14 - 1024#64).toNat = (stackArg s 14).toNat - 1024 := by
    rw [BitVec.toNat_sub, show (1024#64).toNat = 1024 from rfl]; omega
  have toNat_off : ∀ {p : Addr} {d : Nat}, p.toNat + d < 2 ^ 64 → (off p d).toNat = p.toNat + d := fun h => by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- `out`, with the length `n_len`.
  have ho : ∀ {R : Region}, (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint R →
      (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint R := fun h => by rw [← hsi]; exact h
  have hKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ := by rw [← hsi]; exact hp.dKo
  -- What lies in what.
  have sI : Region.Sub ⟨off (stackArg s 13) oEm, (s.gpr .rcx).toNat⟩ ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ :=
    Offset.sub_base _ (by omega)
  have sR : Region.Sub ⟨off (stackArg s 13) oRsa, (stackArg s 14 - 1024#64).toNat * 8⟩
      ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ := Offset.sub_base _ (by rw [hsc]; omega)
  have sA : Region.Sub ⟨fb s, 112⟩ (stkR s) := fun a h => frame_sub s a (Region.sub_prefix (by decide) a h)
  have sRet : Region.Sub ⟨fb s - 8, 8⟩ (stkR s) := ret_sub s
  have sStk : Region.Sub ⟨fb s - 8 - BitVec.ofNat 64 Rsa.X86_64.stackBytes, Rsa.X86_64.stackBytes⟩ (stkR s) := by
    simp only [stkR, fb, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  have dRA : (⟨fb s - 8, 8⟩ : Region).Disjoint ⟨fb s, 112⟩ :=
    (Offset.base_disjoint_below (fb s) (n := 8) (k := 112) (by omega)).symm
  have dKA : (⟨fb s - 8 - BitVec.ofNat 64 Rsa.X86_64.stackBytes, Rsa.X86_64.stackBytes⟩ : Region).Disjoint
      ⟨fb s, 112⟩ := by
    refine Region.Disjoint.sub_left (Offset.base_disjoint_below (fb s) (n := 3256) (k := 112) (by omega)).symm ?_
    simp only [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  have dIR : (⟨off (stackArg s 13) oEm, (s.gpr .rcx).toNat⟩ : Region).Disjoint
      ⟨off (stackArg s 13) oRsa, (stackArg s 14 - 1024#64).toNat * 8⟩ :=
    Offset.disjoint _ (.inl (by omega)) (by omega) (by rw [hsc]; omega)
  have hsA : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region).Disjoint ⟨fb s, 112⟩ := (hp.dKs.sub_left sA).symm
  refine ⟨by omega, by omega, rfl, rfl, ho hp.dOn, ho hp.dOe, (ho hp.dOs).sub_right sI, ho hp.dOp, ho hp.dOq,
    ho hp.dOdp, ho hp.dOdq, ho hp.dOqi, (ho hp.dOs).sub_right sR, (hKo.sub_left sA).symm,
    hp.dns.sub_right sR, hp.des.sub_right sR, dIR, hp.dps.sub_right sR, hp.dqs.sub_right sR, hp.ddps.sub_right sR,
    hp.ddqs.sub_right sR, hp.dqis.sub_right sR, hsA.sub_left sR,
    hKo.sub_left sRet, hp.dKn.sub_left sRet, hp.dKe.sub_left sRet, (hp.dKs.sub_left sRet).sub_right sI,
    hp.dKp.sub_left sRet, hp.dKq.sub_left sRet, hp.dKdp.sub_left sRet, hp.dKdq.sub_left sRet, hp.dKqi.sub_left sRet,
    (hp.dKs.sub_left sRet).sub_right sR, dRA,
    hKo.sub_left sStk, hp.dKn.sub_left sStk, hp.dKe.sub_left sStk, (hp.dKs.sub_left sStk).sub_right sI,
    hp.dKp.sub_left sStk, hp.dKq.sub_left sStk, hp.dKdp.sub_left sStk, hp.dKdq.sub_left sStk, hp.dKqi.sub_left sStk,
    (hp.dKs.sub_left sStk).sub_right sR, dKA,
    by rw [← hsi]; exact hp.wO, hp.wN, hp.wE, by rw [toNat_off (by omega)]; omega, hp.wP, hp.wQ, hp.wDp, hp.wDq,
    hp.wQi, by rw [toNat_off (by omega), hsc]; omega, ⟨hk1, hk2⟩, trivial, trivial, hp.L1, hp.L2, hp.pl1, hp.pl2,
    hp.ql1, hp.ql2, hp.hdpl, hp.hqil, hp.hdql, by unfold Spec.Rsa.scratchWords; rw [hsc]; omega⟩

theorem priv_covers {s t : State} (hp : SPre G s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr) :
    Covers (pRd s ++ pWr s) (t.rd ++ t.wr) ∧ Covers (pWr s) t.wr := by
  have hk2 := hp.k2; have hsl := hp.hsl; have hk1 := hp.k1
  have hsi := hp.hsi
  have c1 : oEm = 2560 := rfl
  have c2 : oRsa = 8192 := rfl
  have hsc : (stackArg s 14 - 1024#64).toNat = (stackArg s 14).toNat - 1024 := by
    rw [BitVec.toNat_sub, show (1024#64).toNat = 1024 from rfl]; omega
  have hfr : frR s ∈ t.wr := by rw [hwr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  have hout : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [pWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hout, 0, z _, by dsimp only; omega⟩
    · exact ⟨_, hscr, oRsa, rfl, by dsimp only; rw [hsc]; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hin : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [hrd]; exact hx)
  simp only [pRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hin _ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hin _ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, List.mem_append_right _ hscr, oEm, rfl, by dsimp only; omega⟩
  · exact ⟨_, hin _ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hin _ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hin _ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hin _ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hin _ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; decide⟩

/-- Bytes apart from a frame's regions. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨p, len⟩ : Region).Disjoint r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

/-- The three regions the function writes. -/
abbrev wrR (s : State) : List Region := [stkR s, outR s, scrR s]

/-- An input, apart from them. -/
theorem in_apart {s : State} {R : Region} (hK : (stkR s).Disjoint R) (hO : (outR s).Disjoint R)
    (hS : R.Disjoint (scrR s)) : ∀ r ∈ wrR s, R.Disjoint r := by
  intro r hr
  simp only [wrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hK.symm
  · exact hO.symm
  · exact hS

theorem priv_call {privN : String} {privC : Prog isa}
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hsp : SpSafe privC) (hd : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes - 8)
    {s t : State} (hp : SPre G s) (hst : t.gpr .rsp = fb s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr)
    (hM : Frame (wrR s) s.mem t.mem)
    (hargs : ∀ i < 14, word t.mem (fb s) (8 * i) = pArg s i) (hdi : t.gpr .rdi = s.gpr .rdi)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call privN privC) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame (wrR s) s.mem t'.mem ∧
      (∀ x, ((frR s).Contains x 1 ∨ (⟨stackArg s 13, oRsa⟩ : Region).Contains x 1) → t'.mem x = t.mem x) ∧
      Spec.Rsa.writtenOutcome t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt t.mem (off (stackArg s 13) oEm) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)) := by
  obtain ⟨hc, hw⟩ := priv_covers hp hrd hwr
  have hsb : Rsa.X86_64.stackBytes = 3248 := rfl
  refine X86_64.WP.callF hv hsp (by omega) (priv_pre hp hst hargs hdi hsi hdx hcx h8 h9) hc hw ?_
  intro t' hrd' hwr' hcs hf ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  have hF := fb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hss : signStack = 3648 := rfl
  have c2 : oRsa = 8192 := rfl
  have c1 : oEm = 2560 := rfl
  have hsc : (stackArg s 14 - 1024#64).toNat = (stackArg s 14).toNat - 1024 := by
    rw [BitVec.toNat_sub, show (1024#64).toNat = 1024 from rfl]; omega
  rw [hst] at hf
  -- What the call writes, within what the function may write.
  have sOut : Region.Sub ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ (outR s) := by
    rw [outR, hp.hsi]; exact fun _ h => h
  have sScr : Region.Sub ⟨off (stackArg s 13) oRsa, (stackArg s 14 - 1024#64).toNat * 8⟩ (scrR s) :=
    Offset.sub_base _ (by rw [hsc]; omega)
  have sBel : Region.Sub (below (fb s) (privC.x86_64Depth + 8)) (stkR s) := by
    simp only [below, fb, stkR, sub_sub']
    exact Offset.sub_below _ (by omega) (by omega)
  refine ⟨hrd', hwr', hcs, hmx, hM.trans (hf.sub fun r hr => ?_), fun x hx => hf x fun r hr hc => ?_, ?_⟩
  · simp only [pWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sOut⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), sScr⟩
    · exact ⟨_, List.mem_cons_self .., sBel⟩
  · simp only [pWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have dFb : (frR s).Disjoint (below (fb s) (privC.x86_64Depth + 8)) :=
      Offset.base_disjoint_below (fb s) (by omega)
    rcases hx with hx | hx <;> rcases hr with rfl | rfl | rfl
    · exact (hp.dKo.sub_left (frame_sub s)) x hx (sOut x hc)
    · exact (hp.dKs.sub_left (frame_sub s)) x hx (sScr x hc)
    · exact dFb x hx hc
    · exact (hp.dOs.symm.sub_left (Region.sub_prefix (by omega))) x hx (sOut x hc)
    · exact (Offset.base_disjoint (stackArg s 13) (e := oRsa) (n := (stackArg s 14 - 1024#64).toNat * 8)
        (k := oRsa) (le_refl _) (by rw [hsc]; omega)) x hx hc
    · exact ((hp.dKs.sub_left sBel).symm.sub_left (Region.sub_prefix (by omega))) x hx hc
  · have hE : ∀ i < 14, stackArg (t.callEntry.withRegions (pRd s) (pWr s)) i = pArg s i :=
      fun i hi => (stackArg_call hp hst _ _ hi).trans (hargs i hi)
    have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
      rw [State.callEntry_mem, hst]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
    have fSE : Frame (wrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
    have b : ∀ {R : Region}, (stkR s).Disjoint R → (outR s).Disjoint R → R.Disjoint (scrR s) → R.len ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
      fun hK hO hS hl => bytesAt_frame fSE (in_apart hK hO hS) hl
    have bEm : Spec.Rsa.bytesAt t.callEntry.mem (off (stackArg s 13) oEm) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (off (stackArg s 13) oEm) (s.gpr .rcx).toNat :=
      bytesAt_frame fE (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ((hp.dKs.sub_left (ret_sub s)).symm.sub_left (Offset.sub_base _ (by omega)))) (by omega)
    simp only [chkContract, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
      hdi, hdx, hcx, h8, h9, hE 0 (by decide), hE 2 (by decide), hE 3 (by decide), hE 4 (by decide),
      hE 5 (by decide), hE 6 (by decide), hE 8 (by decide), hE 10 (by decide), pArg, Nat.reduceSub, hm₂,
      hg₂ .rax (by decide)] at hpost
    rw [b (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hp.dKn hp.dOn hp.dns (by have := hp.wN; dsimp only; omega),
      b (R := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩) hp.dKe hp.dOe hp.des (by have := hp.wE; dsimp only; omega),
      bEm,
      b (R := ⟨stackArg s 0, (stackArg s 1).toNat⟩) hp.dKp hp.dOp hp.dps (by have := hp.wP; dsimp only; omega),
      b (R := ⟨stackArg s 2, (stackArg s 3).toNat⟩) hp.dKq hp.dOq hp.dqs (by have := hp.wQ; dsimp only; omega),
      b (R := ⟨stackArg s 4, (stackArg s 1).toNat⟩) (by rw [← hp.hdpl]; exact hp.dKdp) (by rw [← hp.hdpl]; exact hp.dOdp)
        (by rw [← hp.hdpl]; exact hp.ddps) (by have := hp.wDp; have := hp.hdpl; dsimp only; omega),
      b (R := ⟨stackArg s 6, (stackArg s 3).toNat⟩) (by rw [← hp.hdql]; exact hp.dKdq) (by rw [← hp.hdql]; exact hp.dOdq)
        (by rw [← hp.hdql]; exact hp.ddqs) (by have := hp.wDq; have := hp.hdql; dsimp only; omega),
      b (R := ⟨stackArg s 8, (stackArg s 1).toNat⟩) (by rw [← hp.hqil]; exact hp.dKqi) (by rw [← hp.hqil]; exact hp.dOqi)
        (by rw [← hp.hqil]; exact hp.dqis) (by have := hp.wQi; have := hp.hqil; dsimp only; omega)] at hpost
    exact hpost

end VG.Proof.RsaPss.X86_64
