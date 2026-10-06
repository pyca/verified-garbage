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

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
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
    (hsp : SpSafe privC) (hd : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)
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

/-! ## The stack arguments -/

/-- Stack argument `j` (of ours) to word `j + 2` of the frame. -/
def cpyArg (j : Nat) : List Instr := [.mov .rax (.mem (arg j)), .store (sp (16 + 8 * j)) .rax]

def privTail : List Instr :=
  scr .rax oEm ++ [.store (sp 0) .rax, .mov .rax (.mem (sp sK)), .store (sp 8) .rax] ++
  scr .rax oRsa ++ [.store (sp 96) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024),
    .store (sp 104) .rax] ++
  [.mov .rdi (.mem (sp sOut)), .mov .rsi (.mem (sp sK)), .mov .rdx (.mem (sp sN)), .mov .rcx (.mem (sp sK)),
    .mov .r8 (.mem (sp sE)), .mov .r9 (.mem (sp sEl))]

theorem privArgs_eq : privArgs = (List.range 10).flatMap cpyArg ++ privTail := rfl

/-- Our stack arguments, still where they were. -/
def ArgsKept (s : State) (m : Mem) : Prop := ∀ j < 15, m.readW (stackArgAddr s j) 64 = stackArg s j

theorem ArgsKept.write {s : State} (hp : SPre G s) {m : Mem} (h : ArgsKept s m) {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : ArgsKept s (m.writeW (off (fb s) d) v) := fun j hj => by
  have hF := fb_toNat hp
  have := hp.sp2
  rw [← argAddr, Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold frameBytes at *; omega)) (by omega)
    (by omega)) (by decide)]
  exact (congrArg (fun a => m.readW a 64) (argAddr s j)).trans (h j hj)

theorem cpyArg_ok {s : State} (hp : SPre G s) {u : State} {S : Addr} (L : Lay u (fb s) S) (hrd : u.rd = s.rd)
    (hA : ArgsKept s u.mem) {j : Nat} (hj : j < 10) :
    WP isa (.block (cpyArg j)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) (16 + 8 * j)) (stackArg s j) := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    refine ⟨⟨stackArgAddr s 0, 120⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
    rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) (16 + 8 * j)) (stackArg s j)) ?_ rfl
    |> WP.mono <| fun u' ⟨hm, k⟩ => ⟨k, hm⟩
  have hv : u.mem.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
    rw [argAddr]; exact hA j (by omega)
  xrun [cpyArg, arg, ea_sp, L.rsp, hin, hv, L.st (d := 16 + 8 * j) (by unfold frameBytes; omega)]

/-- The words the copies leave. -/
def cpW (s : State) (W : Nat → BitVec 64) (n : Nat) (i : Nat) : BitVec 64 :=
  if 2 ≤ i ∧ i < 2 + n then stackArg s (i - 2) else W i

theorem cpys_ok {s : State} (hp : SPre G s) {S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} :
    ∀ n ≤ 10, ∀ u : State, Lay u (fb s) S → u.rd = s.rd → ArgsKept s u.mem → Rep u.mem (fb s) S V W →
    WP isa (.block ((List.range n).flatMap cpyArg)) u fun u' => Keep [.rax] u u' ∧ Lay u' (fb s) S ∧
      ArgsKept s u'.mem ∧ Rep u'.mem (fb s) S V (cpW s W n)
  | 0, _, u, L, _, hA, R => WP.block_nil ⟨Keep.refl _ _, L, hA, by
      refine (congrArg (fun W' => Rep u.mem (fb s) S V W') (funext fun i => ?_)).mp R
      simp only [cpW]; rw [ifn (by omega)]⟩
  | n + 1, hn, u, L, hrd, hA, R => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (cpys_ok hp n (by omega) u L hrd hA R) fun u1 ⟨k1, L1, hA1, R1⟩ => ?_
    refine WP.mono (cpyArg_ok hp L1 (k1.2.1.trans hrd) hA1 (j := n) (by omega)) fun u2 ⟨k2, hm2⟩ => ?_
    have R2 := R1.wf L1.geo (k := n + 2) (by unfold nW frameBytes; omega) (stackArg s n)
    rw [show off (fb s) (8 * (n + 2)) = off (fb s) (16 + 8 * n) by congr 1; omega, ← hm2] at R2
    have R2' : Rep u2.mem (fb s) S V (cpW s W (n + 1)) := by
      refine (congrArg (fun W' => Rep u2.mem (fb s) S V W') (funext fun i => ?_)).mp R2
      simp only [upd, cpW]
      by_cases hi : i = n + 2
      · subst hi; rw [ifp rfl, ifp (by omega), show n + 2 - 2 = n by omega]
      · rw [ifn hi]
        by_cases h' : 2 ≤ i ∧ i < 2 + n
        · rw [ifp h', ifp (by omega)]
        · rw [ifn h', ifn (by omega)]
    refine ⟨(k1.trans k2).mono (by decide), L1.of_rep' R1 R2' (by simp only [cpW]; rw [ifn (by omega), ifn (by omega)]) (k2.gpr (by decide)) k2.2.2,
      by rw [hm2]; exact hA1.write hp (by unfold frameBytes; omega) _, R2'⟩

theorem off_zero (p : Addr) : off p 0 = p := BitVec.add_zero p

/-- The private-key operation's arguments: its stack arguments in the
frame's first words, the rest of ours kept, and its registers. -/
theorem privArgs_ok {s : State} (hp : SPre G s) {u : State} (L : Lay u (fb s) (stackArg s 13)) (hrd : u.rd = s.rd)
    (hA : ArgsKept s u.mem) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 13) V W)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rcx) (h18 : W 18 = s.gpr .rdx) (h19 : W 19 = s.gpr .r8)
    (h20 : W 20 = s.gpr .r9) (h22 : W 22 = stackArg s 14) :
    WP isa (.block privArgs) u fun u' => Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Lay u' (fb s) (stackArg s 13) ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 13) V W' ∧ (∀ i < 14, W' i = pArg s i) ∧ (∀ i < nW, 14 ≤ i → W' i = W i)) ∧
      u'.gpr .rdi = s.gpr .rdi ∧ u'.gpr .rsi = s.gpr .rcx ∧ u'.gpr .rdx = s.gpr .rdx ∧ u'.gpr .rcx = s.gpr .rcx ∧
      u'.gpr .r8 = s.gpr .r8 ∧ u'.gpr .r9 = s.gpr .r9 := by
  rw [privArgs_eq, WP.block_append_iff]
  refine WP.mono (cpys_ok hp 10 (le_refl _) u L hrd hA R) fun u1 ⟨k1, L1, _, R1⟩ => ?_
  have G' := L1.geo
  set W1 := cpW s W 10 with hW1
  have c : ∀ i, 14 ≤ i → W1 i = W i := fun i hi => by simp only [hW1, cpW]; rw [ifn (by omega)]
  have hs : u1.mem.readW (off (fb s) sScr) 64 = stackArg s 13 := L1.slot
  set S := stackArg s 13
  have Ra := R1.wf G' (k := 0) (by decide) (off S oEm)
  have Rb := Ra.wf G' (k := 1) (by decide) (s.gpr .rcx)
  have Rc := Rb.wf G' (k := 12) (by decide) (off S oRsa)
  have Rd := Rc.wf G' (k := 13) (by decide) (stackArg s 14 - BitVec.ofNat 64 1024)
  simp only [Nat.reduceMul, off_zero] at Ra Rb Rc Rd
  have hst0 : InRegions u1.wr (fb s) 8 := by simpa only [off_zero] using L1.st (d := 0) (by decide)
  have f1 : (u1.mem.writeW (fb s) (off S oEm)).readW (off (fb s) sK) 64 = s.gpr .rcx := by
    rw [Ra.rd (d := sK) 17 rfl (by decide)]; simp [upd, c, h17]
  have f2 : ((u1.mem.writeW (fb s) (off S oEm)).writeW (off (fb s) 8) (s.gpr .rcx)).readW
      (off (fb s) sScr) 64 = S := by
    rw [Rb.rd (d := sScr) 21 rfl (by decide)]; simp only [upd, Nat.reduceEqDiff, ite_false]
    exact (R1.rd (d := sScr) 21 rfl (by decide)).symm.trans hs
  have f3 : (((u1.mem.writeW (fb s) (off S oEm)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW
      (off (fb s) 96) (off S oRsa)).readW (off (fb s) sScrLen) 64 = stackArg s 14 := by
    rw [Rc.rd (d := sScrLen) 22 rfl (by decide)]; simp [upd, c, h22]
  set m4 := ((((u1.mem.writeW (fb s) (off S oEm)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW
      (off (fb s) 96) (off S oRsa)).writeW (off (fb s) 104) (stackArg s 14 - BitVec.ofNat 64 1024)) with hm4
  have g : ∀ k, 14 ≤ k → k < nW → m4.readW (off (fb s) (8 * k)) 64 = W k := fun k hk hk' => by
    refine (Rd.fr k hk').trans ?_; simp only [upd]; rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega), c k hk]
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u' => u'.mem = m4 ∧
      u'.gpr .rdi = s.gpr .rdi ∧ u'.gpr .rsi = s.gpr .rcx ∧ u'.gpr .rdx = s.gpr .rdx ∧ u'.gpr .rcx = s.gpr .rcx ∧
      u'.gpr .r8 = s.gpr .r8 ∧ u'.gpr .r9 = s.gpr .r9) ?_ rfl) fun u2 ⟨⟨hm, h1, h2, h3, h4, h5, h6⟩, k2⟩ => ?_
  · xrun [privTail, scr, List.cons_append, List.nil_append, ea_sp, L1.rsp, L1.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), off_plus, hst0,
      L1.st (d := 8) (by decide), L1.st (d := 96) (by decide), L1.st (d := 104) (by decide),
      L1.ld (d := sK) (by decide), L1.ld (d := sScrLen) (by decide), L1.ld (d := sOut) (by decide),
      L1.ld (d := sN) (by decide), L1.ld (d := sE) (by decide), L1.ld (d := sEl) (by decide), f1, f2, f3,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oRsa < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show 1024 < 2 ^ 31 by decide),
      show m4.readW (off (fb s) sOut) 64 = s.gpr .rdi from (g 16 (by decide) (by decide)).trans h16,
      show m4.readW (off (fb s) sK) 64 = s.gpr .rcx from (g 17 (by decide) (by decide)).trans h17,
      show m4.readW (off (fb s) sN) 64 = s.gpr .rdx from (g 18 (by decide) (by decide)).trans h18,
      show m4.readW (off (fb s) sE) 64 = s.gpr .r8 from (g 19 (by decide) (by decide)).trans h19,
      show m4.readW (off (fb s) sEl) 64 = s.gpr .r9 from (g 20 (by decide) (by decide)).trans h20]
    rw [show BitVec.signExtend 64 (1024 : BitVec 32) = BitVec.ofNat 64 1024 by decide]
    exact ⟨rfl, (g 16 (by decide) (by decide)).trans h16, (g 17 (by decide) (by decide)).trans h17,
      (g 18 (by decide) (by decide)).trans h18, (g 17 (by decide) (by decide)).trans h17,
      (g 19 (by decide) (by decide)).trans h19, (g 20 (by decide) (by decide)).trans h20⟩
  have R2 : Rep u2.mem (fb s) S V _ := hm ▸ Rd
  refine ⟨(k1.trans k2).mono (by decide), L1.of_rep' R1 R2 (by simp [upd]) (k2.gpr (by decide)) k2.2.2,
    ⟨_, R2, fun i hi => ?_, fun i hi h14 => ?_⟩, h1, h2, h3, h4, h5, h6⟩
  · simp only [upd, hW1, cpW, pArg]
    rcases (show i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i < 12) ∨ i = 12 ∨ i = 13 by omega) with h | h | h | h | h
    · subst h; simp; rfl
    · subst h; simp
    · rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega), ifp h]
      match i, h with
      | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ => rfl
    · subst h; simp; rfl
    · subst h; simp
  · simp only [upd]
    rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega), c i h14]

end VG.Proof.RsaPss.X86_64
