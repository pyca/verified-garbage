import VerifiedGarbage.Proof.RsaOaep.X86_64.EncFrame
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncEm
import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub

/-!
# RSAES-OAEP encryption on x86-64: the call of `vg_rsa_public_checked`

Its arguments (`pubArgs_ok`), and the call (`encPub_call`): `out` receives
RSAEP of `EM` (the first `k` bytes of our working space), or zeros. Memory
outside the stack the function uses, `out` and the working space reads as
on entry (`FrE`).
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.RsaPkcs1Sig.X86_64 (PubImpl pubChk pubChkPost pubChecked)

variable {H : Spec.Mgf1.Hash}

/-- `out`. -/
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩

/-- The working space. -/
def scrR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩

/-- Memory changed only in the stack the function uses, `out` and the
working space. -/
def FrE (s : State) (m : Mem) : Prop := Frame [stkR s, outR s, scrR s] s.mem m

/-- The bytes of a region apart from those, as on entry. -/
theorem FrE.bytes {s : State} {m : Mem} (h : FrE s m) {p : Addr} {len : Nat} (hk : (stkR s).Disjoint ⟨p, len⟩)
    (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => Frame.bytes h (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

/-- A step that changed memory only within the writable regions of a state
in the frame and the 16 bytes below it. -/
theorem FrE.step {s : State} {m m' : Mem} (h : FrE s m) {ws : List Region}
    (hws : ws = [frR s, outR s, scrR s]) (h' : Frame (ws ++ [below (fb s) 16]) m m') : FrE s m' :=
  h.trans (h'.sub fun r hr => by
    rw [hws] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., frame_sub s⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., ret_sub s⟩)

theorem EPre.wr {s : State} (hp : EPre H s) : (allocState frameBytes s).wr = [frR s, outR s, scrR s] := by
  simp [allocState, hp.hwr, outR, scrR]

/-! ## The arguments -/

theorem pubArgs_ok {s u : State} (L : Lay u (fb s) (stackArg s 5)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 5) V W) (hW : ∀ k, 21 ≤ k → k ≤ 26 → W k = encW s k) :
    WP isa (.block pubArgs) u fun u' => Lay u' (fb s) (stackArg s 5) ∧
      Keep [.rax, .rdx, .rcx, .r9, .rdi, .rsi, .r8] u u' ∧
      Rep u'.mem (fb s) (stackArg s 5) V (upd (upd (upd (upd W 0 (off (stackArg s 5) oEm)) 1 (s.gpr .rcx)) 2
        (off (stackArg s 5) oRsa)) 3 (stackArg s 6 - 1024)) ∧
      u'.gpr .rdi = s.gpr .rdi ∧ u'.gpr .rsi = s.gpr .rcx ∧ u'.gpr .rdx = s.gpr .rdx ∧ u'.gpr .rcx = s.gpr .rcx ∧
      u'.gpr .r8 = s.gpr .r8 ∧ u'.gpr .r9 = s.gpr .r9 := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have G' := L.geo
  have e : ∀ k, 21 ≤ k → k ≤ 26 → W k = encW s k := hW
  have w21 : W 21 = s.gpr .rdi := (e 21 (by omega) (by omega)).trans (by simp [encW, upd])
  have w22 : W 22 = s.gpr .rdx := (e 22 (by omega) (by omega)).trans (by simp [encW, upd])
  have w23 : W 23 = s.gpr .rcx := (e 23 (by omega) (by omega)).trans (by simp [encW, upd])
  have w24 : W 24 = s.gpr .r8 := (e 24 (by omega) (by omega)).trans (by simp [encW, upd])
  have w25 : W 25 = s.gpr .r9 := (e 25 (by omega) (by omega)).trans (by simp [encW, upd])
  have w26 : W 26 = stackArg s 6 := (e 26 (by omega) (by omega)).trans (by simp [encW, upd])
  have R1 := (((R.wf G' (k := 0) (by decide) (off (stackArg s 5) oEm)).wf G' (k := 1) (by decide) (s.gpr .rcx)).wf G'
    (k := 2) (by decide) (off (stackArg s 5) oRsa)).wf G' (k := 3) (by decide) (stackArg s 6 - 1024)
  have z : off (fb s) (8 * 0) = fb s := BitVec.add_zero _
  rw [z, show 8 * 1 = 8 from rfl, show 8 * 2 = 16 from rfl, show 8 * 3 = 24 from rfl] at R1
  have h0 : InRegions u.wr (fb s) 8 := by rw [← z]; exact L.st (d := 0) (by decide)
  refine WP.mono (WP.keep [.rax, .rdx, .rcx, .r9, .rdi, .rsi, .r8] (Q := fun u' => u'.mem =
      (((u.mem.writeW (fb s) (off (stackArg s 5) oEm)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW
        (off (fb s) 16) (off (stackArg s 5) oRsa)).writeW (off (fb s) 24) (stackArg s 6 - 1024) ∧
      u'.gpr .rdi = s.gpr .rdi ∧ u'.gpr .rsi = s.gpr .rcx ∧ u'.gpr .rdx = s.gpr .rdx ∧ u'.gpr .rcx = s.gpr .rcx ∧
      u'.gpr .r8 = s.gpr .r8 ∧ u'.gpr .r9 = s.gpr .r9) ?_ rfl) fun u' ⟨⟨hm, h1, h2, h3, h4, h5, h6⟩, kk⟩ =>
    ⟨L.of_rep' R (by rw [hm]; exact R1) (by simp [upd]) (kk.gpr (by decide)) kk.2.2, kk, by rw [hm]; exact R1,
      h1, h2, h3, h4, h5, h6⟩
  xrun [pubArgs, scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sK) (by decide), L.ld (d := sScrLen) (by decide),
    L.ld (d := sOut) (by decide), L.ld (d := sN) (by decide), L.ld (d := sE) (by decide),
    L.ld (d := sEl) (by decide), hs, R.slot (d := sK) (k := 23) rfl (by decide) w23,
    R.slot (d := sScrLen) (k := 26) rfl (by decide) w26,
    h0, L.st (d := 8) (by decide), L.st (d := 16) (by decide), L.st (d := 24) (by decide),
    R1.slot (d := sOut) (k := 21) rfl (by decide) (v := s.gpr .rdi) (by simp [upd, w21]),
    R1.slot (d := sK) (k := 23) rfl (by decide) (v := s.gpr .rcx) (by simp [upd, w23]),
    R1.slot (d := sN) (k := 22) rfl (by decide) (v := s.gpr .rdx) (by simp [upd, w22]),
    R1.slot (d := sE) (k := 24) rfl (by decide) (v := s.gpr .r8) (by simp [upd, w24]),
    R1.slot (d := sEl) (k := 25) rfl (by decide) (v := s.gpr .r9) (by simp [upd, w25]),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oRsa < 2 ^ 31 by decide),
    show BitVec.signExtend 64 (1024 : BitVec 32) = 1024 from by decide]

/-! ## The call -/

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {t : State} {F : Addr} (hsp : t.gpr .rsp = F) (hF : 8 ≤ F.toNat) (rd wr : List Region)
    {i : Nat} (hi : F.toNat + 8 * i + 8 ≤ 2 ^ 64) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (off F (8 * i)) 64 := by
  have hb : F - 8 + BitVec.ofNat 64 (8 * (i + 1)) = off F (8 * i) := by
    simp only [off]
    rw [show 8 * (i + 1) = 8 + 8 * i by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
      show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]
  have hsep := Offset.sep (F - 8) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega) (by omega) (by omega)
  rw [show F - 8 + BitVec.ofNat 64 0 = F - 8 from BitVec.add_zero _, hb] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, hb]
  exact Mem.readW_writeW_sep hsep (by decide)

/-- The working space the call gets: ours ends at `oRsa`. -/
def rsaR (s : State) : Region := ⟨off (stackArg s 5) oRsa, (stackArg s 6 - 1024).toNat * 8⟩

/-- What the call reads: `n`, `e`, `EM` and its stack arguments. -/
def pubRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨off (stackArg s 5) oEm, (s.gpr .rcx).toNat⟩,
    ⟨fb s, 32⟩]

/-- What it writes: `out` and the rest of the working space. -/
def pubWr (s : State) : List Region := [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩, rsaR s]

theorem rsa_toNat {s : State} (hp : EPre H s) :
    (stackArg s 6 - 1024).toNat = (stackArg s 6).toNat - 1024 ∧
      (off (stackArg s 5) oRsa).toNat = (stackArg s 5).toNat + oRsa := by
  have := hp.hsl; have := hp.wS; have := hp.k1
  constructor
  · rw [BitVec.toNat_sub, show (1024 : BitVec 64).toNat = 1024 from rfl]; omega
  · simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa; omega

theorem rsa_sub {s : State} (hp : EPre H s) : Region.Sub (rsaR s) (scrR s) := by
  have ⟨h1, h2⟩ := rsa_toNat hp
  have := hp.hsl
  simp only [rsaR, scrR]
  rw [h1]
  exact Offset.sub_base _ (by unfold oRsa; omega)

theorem em_sub {s : State} (hp : EPre H s) : Region.Sub ⟨off (stackArg s 5) oEm, (s.gpr .rcx).toNat⟩ (scrR s) := by
  have := hp.hsl; have := hp.k2
  exact Offset.sub_base _ (by unfold oEm; omega)

theorem pub_pre {s t : State} (hp : EPre H s) (hsp : t.gpr .rsp = fb s) (F₀ : Addr) (hF₀ : F₀ = fb s)
    (hw0 : t.mem.readW (off F₀ (8 * 0)) 64 = off (stackArg s 5) oEm) (hw1 : t.mem.readW (off F₀ (8 * 1)) 64 = s.gpr .rcx)
    (hw2 : t.mem.readW (off F₀ (8 * 2)) 64 = off (stackArg s 5) oRsa)
    (hw3 : t.mem.readW (off F₀ (8 * 3)) 64 = stackArg s 6 - 1024)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    pubChk.pre (t.callEntry.withRegions (pubRd s) (pubWr s)) := by
  subst hF₀
  have hF := fb_toNat hp
  have hsp1 := hp.sp1; have hsp2 := hp.sp2
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) i = t.mem.readW (off (fb s) (8 * i)) 64 :=
    fun i hi => stackArg_entry hsp (by unfold encStack frameBytes at *; omega) _ _ (by unfold frameBytes at *; omega)
  have hA : stackArgAddr (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = fb s := by
    simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp]
    rw [show 8 * (0 + 1) = 8 from rfl, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]
  simp only [pubChk, VG.Proof.Bignum.X86_64.pubContract, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp, hA,
    hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide), hw0, hw1, hw2, hw3]
  have hsi' := hp.hsi
  have hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have ⟨r1, r2⟩ := rsa_toNat hp
  have e8 : fb s - 8 = fb s - BitVec.ofNat 64 8 := rfl
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) = outR s := by simp [outR, hsi']
  have sF : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := Offset.sub_below (s.gpr .rsp) (a := frameBytes) (n := 32) (b := encStack) (m := encStack)
      (by decide) (by decide)
    exact this
  have sR : Region.Sub ⟨fb s - 8, 8⟩ (stkR s) := by
    rw [e8]
    exact fun x h => ret_sub s x (Offset.sub_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide)
      (by decide) x h)
  have dRF : Region.Disjoint ⟨fb s - 8, 8⟩ ⟨fb s, 32⟩ := by
    rw [e8]; exact (Offset.base_disjoint_below (fb s) (n := 8) (k := 32) (by omega)).symm
  have dEmR : Region.Disjoint ⟨off (stackArg s 5) oEm, (s.gpr .rcx).toNat⟩ (rsaR s) := by
    simp only [rsaR]; rw [r1]
    exact Offset.disjoint _ (.inl (by unfold oEm oRsa; omega)) (by unfold oEm; omega) (by unfold oRsa; omega)
  have em := em_sub hp
  have rs := rsa_sub hp
  have dSo : (scrR s).Disjoint (outR s) := hp.d_out_scr.symm
  have dSk : (scrR s).Disjoint (stkR s) := hp.d_stk_scr.symm
  have hf8 : (fb s - 8).toNat = (fb s).toNat - 8 := by
    rw [e8, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold encStack frameBytes at *; omega
  have dOF : (outR s).Disjoint ⟨fb s, 32⟩ := hp.d_stk_out.symm.sub_right sF
  refine ⟨by rw [hf8]; unfold frameBytes at *; omega, rfl, rfl,
    by rw [hout]; exact hp.d_out_n, by rw [hout]; exact hp.d_out_e, by rw [hout]; exact dSo.symm.sub_right em,
    by rw [hout]; exact dSo.symm.sub_right rs, by rw [hout]; exact dOF,
    hp.d_n_scr.sub_right rs, hp.d_e_scr.sub_right rs, dEmR, (dSk.sub_right sF).sub_left rs,
    by rw [hout]; exact (hp.d_stk_out).sub_left sR, hp.d_stk_n.sub_left sR, hp.d_stk_e.sub_left sR,
    (dSk.symm.sub_left sR).sub_right em, (dSk.symm.sub_left sR).sub_right rs, dRF,
    by rw [← hsi']; exact hp.wO, hp.wN, hp.wE,
    by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEm; omega,
    by rw [r1, r2]; unfold oRsa; omega,
    ⟨hk1, hk2⟩, trivial, trivial, hp.L1, hp.L2, by rw [r1]; unfold Spec.Rsa.scratchWords; omega⟩

theorem pub_covers {s t : State} (hp : EPre H s) (hrd : t.rd = s.rd) (hwr : t.wr = [frR s, outR s, scrR s]) :
    Covers (pubRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  have hk2 := hp.k2; have hsl := hp.hsl; have hsi := hp.hsi
  have ⟨r1, r2⟩ := rsa_toNat hp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pubWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [pubWr, rsaR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hwr]
    rcases hr with rfl | rfl
    · exact ⟨outR s, by simp, 0, z _, by simp only [outR]; omega⟩
    · exact ⟨scrR s, by simp, oRsa, rfl, by simp only [scrR]; rw [r1]; unfold oRsa; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  simp only [pubRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨scrR s, List.mem_append_right _ (by rw [hwr]; simp), oEm, rfl, by simp only [scrR]; unfold oEm; omega⟩
  · exact ⟨frR s, List.mem_append_right _ (by rw [hwr]; simp), 0, z _, by dsimp only; unfold frameBytes; omega⟩

/-- The call of `vg_rsa_public_checked`: `out` holds RSAEP of `EM`, or zeros. -/
theorem encPub_call {s t : State} (hp : EPre H s) (L : Lay t (fb s) (stackArg s 5)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 5) V W) (hrd : t.rd = s.rd)
    (hwr : t.wr = [frR s, outR s, scrR s]) (hf : FrE s t.mem)
    (hw0 : W 0 = off (stackArg s 5) oEm) (hw1 : W 1 = s.gpr .rcx) (hw2 : W 2 = off (stackArg s 5) oRsa)
    (hw3 : W 3 = stackArg s 6 - 1024)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call pubChecked.name pubChecked.code) t fun t' =>
      Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          ((List.range (s.gpr .rcx).toNat).map fun i => V (oEm + i))) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧ FrE s t'.mem := by
  have hk2 := hp.k2; have hsl := hp.hsl
  obtain ⟨hc, hw⟩ := pub_covers hp hrd hwr
  have rd : ∀ i < 4, t.mem.readW (off (fb s) (8 * i)) 64 = W i := fun i hi => R.rd i rfl (by unfold nW frameBytes; omega)
  refine WP.call_mx (k := pubChk) pubChecked.ok pubChecked.nosp (by rw [pubChecked.depth]; decide)
    (pub_pre hp L.rsp (fb s) rfl ((rd 0 (by decide)).trans hw0) ((rd 1 (by decide)).trans hw1)
      ((rd 2 (by decide)).trans hw2) ((rd 3 (by decide)).trans hw3) hdi hsi hdx hcx h8 h9) hc hw ?_
  intro s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [pubChecked.depth, L.rsp] at hfr
  have hE : stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = off (stackArg s 5) oEm := by
    have hF := fb_toNat hp
    rw [stackArg_entry L.rsp (by have := hp.sp1; unfold encStack frameBytes at *; omega) _ _
      (by have := hp.sp2; unfold frameBytes at *; omega)]
    exact (rd 0 (by decide)).trans hw0
  have hfe : Frame [below (fb s) 16] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, L.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide) (by decide))
  have hfE : FrE s t.callEntry.mem :=
    hf.trans (hfe.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
  have b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    FrE.bytes hfE hk ho hs hl
  have hem : Spec.Rsa.bytesAt t.callEntry.mem (off (stackArg s 5) oEm) (s.gpr .rcx).toNat =
      (List.range (s.gpr .rcx).toNat).map fun i => V (oEm + i) := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [off_plus, ← R.scr _ (by unfold oEm oRsa; omega)]
    have := Frame.bytes hfe (R := ⟨off (stackArg s 5) (oEm + i), 1⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (L.dRS.sub_right (Offset.sub_base _ (by unfold oEm oRsa; omega))).symm)
      (show 1 ≤ 2 ^ 64 by decide) (i := 0) (show 0 < 1 by decide)
    simp only [BitVec.add_zero] at this
    exact this
  simp only [pubChk, pubChkPost, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hdx, hcx, h8, h9, hE, hm₂, hg₂ .rax (by decide)]
    at hpost
  rw [b hp.d_stk_n hp.d_out_n hp.d_n_scr.symm (by have := hp.wN; omega),
    b hp.d_stk_e hp.d_out_e hp.d_e_scr.symm (by have := hp.wE; omega), hem] at hpost
  refine ⟨hpost, hrd', hwr', hcs, hmx, FrE.step hf (ws := t.wr) hwr ?_⟩
  refine hfr.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨outR s, List.mem_append_left _ (by rw [hwr]; simp), by simp only [outR, hp.hsi]; exact fun _ h => h⟩
    · exact ⟨scrR s, List.mem_append_left _ (by rw [hwr]; simp), rsa_sub hp⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨below (fb s) 16, List.mem_append_right _ (List.mem_singleton_self _),
      Offset.sub_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide)⟩

end VG.Proof.RsaOaep.X86_64
