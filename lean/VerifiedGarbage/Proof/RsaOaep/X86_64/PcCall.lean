module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCtx
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: the call

The original arguments of the public operation, then `pre` and `pre_len`
from the stack arguments 8 and 9 (`pubArgs_ok`); the precondition of
`vg_rsa_public_precomputed_checked` (`call_pre`), and what the call leaves
(`call_ok`): `out` holds RSAEP of `EM` if `pre` holds the values for `n`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)

variable {H : Spec.Mgf1.Hash}

/-! ## The arguments -/

theorem arg_in {s t : State} (hp : PPre H s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 12) :
    InRegions (t.rd ++ t.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
  rw [argAddr, hrd]
  apply (Covers.one hp.args).left
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [stackArgAddr_j s j]
  exact Offset.contains_base _ (by omega) (by omega)

theorem arg_keep {s : State} (hp : PPre H s) {m : Mem} (hf : FrE s m) {j : Nat} (hj : j < 12) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := argsR s) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.argsStack
    · exact hp.argsOut
    · exact hp.argsScr

/-- `pre` and `pre_len` in place of `n` and `n_len`. -/
theorem load_pre {s t : State} (hp : PPre H s) (hsp : t.gpr .rsp = fb s) (hrd : t.rd = s.rd) (hf : FrE s t.mem) :
    WP isa (.block [.mov .rdx (.mem (arg 8)), .mov .rcx (.mem (arg 9))]) t fun u =>
      Keep [.rdx, .rcx] t u ∧ u.mem = t.mem ∧ u.gpr .rdx = stackArg s 8 ∧ u.gpr .rcx = stackArg s 9 := by
  refine WP.keep [.rdx, .rcx] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  have i8 := arg_in hp hrd (show 8 < 12 by decide)
  have i9 := arg_in hp hrd (show 9 < 12 by decide)
  have r8 := arg_keep hp hf (show 8 < 12 by decide)
  have r9 := arg_keep hp hf (show 9 < 12 by decide)
  xrun [arg, ea_sp, hsp, i8, i9, r8, r9]

/-! ## The call -/

/-- What `vg_rsa_public_precomputed_checked` reads: `pre`, `e`, `EM` and its
stack arguments. -/
def callRd (s : State) : List Region :=
  [preR s, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨off (stackArg s 6) oEm, (s.gpr .rcx).toNat⟩, ⟨fb s, 32⟩]

theorem call_pre {s t : State} (hp : PPre H s) (hsp : t.gpr .rsp = fb s)
    (hw0 : t.mem.readW (off (fb s) (8 * 0)) 64 = off (stackArg s 6) oEm) (hw1 : t.mem.readW (off (fb s) (8 * 1)) 64 = s.gpr .rcx)
    (hw2 : t.mem.readW (off (fb s) (8 * 2)) 64 = off (stackArg s 6) oRsa)
    (hw3 : t.mem.readW (off (fb s) (8 * 3)) 64 = stackArg s 7 - 1024)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = stackArg s 8)
    (hcx : t.gpr .rcx = stackArg s 9) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    pdContract.pre (t.callEntry.withRegions (callRd s) (pubWr s)) := by
  have hF := fb_toNat hp.toEPre
  have hsp1 := hp.sp1; have hsp2 := hp.sp2
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) i = t.mem.readW (off (fb s) (8 * i)) 64 :=
    fun i hi => stackArg_entry hsp (by unfold encStack frameBytes at *; omega) _ _ (by unfold frameBytes at *; omega)
  have hA : stackArgAddr (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = fb s := by
    simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp]
    rw [show 8 * (0 + 1) = 8 from rfl, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]
  simp only [pdContract, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp, hA,
    hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide), hw0, hw1, hw2, hw3]
  have hsi' := hp.hsi
  have hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have ⟨r1, r2⟩ := rsa_toNat hp.toEPre
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
  have dEmR : Region.Disjoint ⟨off (stackArg s 6) oEm, (s.gpr .rcx).toNat⟩ (rsaR s) := by
    simp only [rsaR]; rw [r1]
    exact Offset.disjoint _ (.inl (by unfold oEm oRsa; omega)) (by unfold oEm; omega) (by unfold oRsa; omega)
  have em := em_sub hp.toEPre
  have rs := rsa_sub hp.toEPre
  have dSo : (scrR s).Disjoint (outR s) := hp.d_out_scr.symm
  have dSk : (scrR s).Disjoint (stkR s) := hp.d_stk_scr.symm
  have hf8 : (fb s - 8).toNat = (fb s).toNat - 8 := by
    rw [e8, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold encStack frameBytes at *; omega
  have dOF : (outR s).Disjoint ⟨fb s, 32⟩ := hp.d_stk_out.symm.sub_right sF
  refine ⟨by rw [hf8]; unfold frameBytes at *; omega, rfl, rfl,
    by rw [hout]; exact hp.preOut.symm, by rw [hout]; exact hp.d_out_e, by rw [hout]; exact dSo.symm.sub_right em,
    by rw [hout]; exact dSo.symm.sub_right rs, by rw [hout]; exact dOF,
    hp.preScr.sub_right rs, hp.d_e_scr.sub_right rs, dEmR, (dSk.sub_right sF).sub_left rs,
    by rw [hout]; exact (hp.d_stk_out).sub_left sR, hp.preStack.symm.sub_left sR, hp.d_stk_e.sub_left sR,
    (dSk.symm.sub_left sR).sub_right em, (dSk.symm.sub_left sR).sub_right rs, dRF,
    by rw [← hsi']; exact hp.wO, hp.preWrap, hp.wE,
    by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEm; omega,
    by rw [r1, r2]; unfold oRsa; omega,
    ⟨hk1, hk2⟩, hp.preLen, trivial, hp.L1, hp.L2, by rw [r1]; unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; omega⟩

theorem call_covers {s t : State} (hp : PPre H s) (hrd : t.rd = s.rd) (hwr : t.wr = [frR s, outR s, scrR s]) :
    Covers (callRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  obtain ⟨c, cw⟩ := pub_covers hp.toEPre hrd hwr
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) cw.right, cw⟩
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hrd]; exact (Covers.one hp.pre).left
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp [pubRd])).trans c
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp [pubRd])).trans c
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp [pubRd])).trans c

/-- `pre`, unchanged where the function writes. -/
theorem pre_words {s : State} {m : Mem} (hp : PPre H s) (hf : FrE s m) :
    Spec.Rsa.wordsAt m (stackArg s 8) (stackArg s 9).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 8) (stackArg s 9).toNat := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  apply hf.readW (r := preR s) ?_ ?_ (by decide)
  · exact Offset.contains_base _ (by have := List.mem_range.mp hi; omega)
      (by have := hp.preWrap; have := List.mem_range.mp hi; omega)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.preStack
    · exact hp.preOut
    · exact hp.preScr

/-- Whether `pre` holds the values for `n`. -/
def Consistent (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 8) (stackArg s 9).toNat)

/-- The call of `vg_rsa_public_precomputed_checked`: `out` holds RSAEP of
`EM`, or zeros, if `pre` holds the values for `n`. -/
theorem call_ok (v : PublicImpl) {s t : State} (hp : PPre H s) (L : Lay t (fb s) (stackArg s 6)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 6) V W) (hrd : t.rd = s.rd)
    (hwr : t.wr = [frR s, outR s, scrR s]) (hf : FrE s t.mem)
    (hw0 : W 0 = off (stackArg s 6) oEm) (hw1 : W 1 = s.gpr .rcx) (hw2 : W 2 = off (stackArg s 6) oRsa)
    (hw3 : W 3 = stackArg s 7 - 1024)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = stackArg s 8)
    (hcx : t.gpr .rcx = stackArg s 9) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call v.name v.code) t fun t' =>
      (Consistent s → Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          ((List.range (s.gpr .rcx).toNat).map fun i => V (oEm + i)))) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧ StepW (t.wr ++ [below (t.gpr .rsp) 16]) t t' := by
  have hk2 := hp.k2; have hsl := hp.hsl
  obtain ⟨hc, hw⟩ := call_covers hp hrd hwr
  have rd : ∀ i < 4, t.mem.readW (off (fb s) (8 * i)) 64 = W i := fun i hi => R.rd i rfl (by unfold nW frameBytes; omega)
  have hpre := call_pre hp L.rsp ((rd 0 (by decide)).trans hw0) ((rd 1 (by decide)).trans hw1)
      ((rd 2 (by decide)).trans hw2) ((rd 3 (by decide)).trans hw3) hdi hsi hdx hcx h8 h9
  refine WP.of_funs (WP.of_syms (WP.call_mx (s := t) (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩)
    (rd := callRd s) (wr := pubWr s) v.ok v.nosp (by rw [v.depth]; decide) hpre hc hw ?_))
  intro s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx hsy hfu
  rw [v.depth, L.rsp] at hfr
  have hE : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = off (stackArg s 6) oEm := by
    have hF := fb_toNat hp.toEPre
    rw [stackArg_entry L.rsp (by have := hp.sp1; unfold encStack frameBytes at *; omega) _ _
      (by have := hp.sp2; unfold frameBytes at *; omega)]
    exact (rd 0 (by decide)).trans hw0
  have hfe : Frame [below (fb s) 16] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, L.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide) (by decide))
  have hfE : FrE s t.callEntry.mem :=
    hf.trans (hfe.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
  have hem : Spec.Rsa.bytesAt t.callEntry.mem (off (stackArg s 6) oEm) (s.gpr .rcx).toNat =
      (List.range (s.gpr .rcx).toNat).map fun i => V (oEm + i) := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [off_plus, ← R.scr _ (by unfold oEm oRsa; omega)]
    have := Frame.bytes hfe (R := ⟨off (stackArg s 6) (oEm + i), 1⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (L.dRS.sub_right (Offset.sub_base _ (by unfold oEm oRsa; omega))).symm)
      (show 1 ≤ 2 ^ 64 by decide) (i := 0) (show 0 < 1 by decide)
    simp only [BitVec.add_zero] at this
    exact this
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hE, hm₂,
    hg₂ .rax (by decide)] at hpost
  rw [pre_words hp hfE, FrE.bytes hfE hp.d_stk_e hp.d_out_e hp.d_e_scr.symm (by have := hp.wE; omega), hem]
    at hpost
  refine ⟨fun hq => hpost _ (by simp [Spec.Rsa.bytesAt]) hq, hrd', hwr', hcs, hmx, ⟨?_, hfu, hsy⟩⟩
  rw [L.rsp, hwr]
  refine hfr.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨outR s, List.mem_append_left _ (by simp), by simp only [outR, hp.hsi]; exact fun _ h => h⟩
    · exact ⟨scrR s, List.mem_append_left _ (by simp), rsa_sub hp.toEPre⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨below (fb s) 16, List.mem_append_right _ (List.mem_singleton_self _),
      Offset.sub_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide)⟩

end VG.Proof.RsaOaep.X86_64.Pc
