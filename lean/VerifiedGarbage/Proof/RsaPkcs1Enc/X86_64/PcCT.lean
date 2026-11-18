module

import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCall
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCall
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Precomputed
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncFrame
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Precomputed
meta import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncFrame

/-! ### `RsaPkcs1Enc.X86_64.PcContract`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.X86_64.PcCall`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.X86_64.PcCtx`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64: the precondition

The shared contract's precondition, by name (`PPre`): `EPre` for the
original arguments, which the code before and after the call reads as
`vg_rsa_pkcs1_encrypt` does, and the precomputed values `pre` (`pre_len`
words), the stack arguments 6 and 7, which only the call reads.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩

/-- All eight stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 64⟩

/-- The precondition of the original function, and the cache. -/
structure PPre (s : State) : Prop extends EPre s where
  sp3 : (s.gpr .rsp).toNat + 72 ≤ 2 ^ 64
  args : InRegions s.rd (stackArgAddr s 0) 64
  pre : InRegions s.rd (stackArg s 6) ((stackArg s 7).toNat * 8)
  argsOut : (argsR s).Disjoint (outR s)
  argsScr : (argsR s).Disjoint (scrR s)
  argsStack : (argsR s).Disjoint (stkR s)
  preOut : (preR s).Disjoint (outR s)
  preScr : (preR s).Disjoint (scrR s)
  preStack : (preR s).Disjoint (stkR s)
  preWrap : (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64
  preLen : (stackArg s 7).toNat = Spec.Rsa.precomputedWords (s.gpr .rcx).toNat

theorem stackArgs_eight (s : State) :
    (List.range 8).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2,
      stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

theorem pre_of {s : State}
    (h : (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).pre s) : PPre s := by
  sig_pre [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig,
    abi, argRegs, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp3, hrd, hwr, dOn, dOe, dOm, dOp, dOs, dOq, dOa, dns, des, dms, dps, dsq, dsa,
    dRo, -, -, -, -, dRs, -, -, dKo, dKn, dKe, dKm, dKp, dKs, dKq, dKa,
    wO, wN, wE, wM, wP, wS, wQ, ⟨k1, k2⟩, hsi, L1, L2, hml, hpl, hsl, pl⟩ := h
  have ha : Region.Sub ⟨stackArgAddr s 0, 48⟩ ⟨stackArgAddr s 0, 64⟩ := Region.sub_prefix (by decide)
  refine ⟨⟨sp1, by omega_using [sp3], ?_, hwr, dOn, dOe, dOm, dOp, dOs, dOa.sub_right ha, dns, des, dms, dps,
    dsa.sub_right ha, dRo, dRs, dKo, dKn, dKe, dKm, dKp, dKs, dKa.sub_right ha, wO, wN, wE, wM, wP, wS,
    k1, k2, hsi, L1, L2, hml, hpl, hsl⟩,
    sp3, ?_, ?_, dOa.symm, dsa.symm, dKa.symm, dOq.symm, dsq.symm, dKq.symm, wQ, pl⟩
  · rw [hrd]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨stackArgAddr s 0, 64⟩, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; decide⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Pc

end

end

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64: the call

The original arguments of the public operation, then `pre` and `pre_len`
from the stack arguments 6 and 7 (`callArgs_ok`); the precondition of
`vg_rsa_public_precomputed_checked` (`call_pre`), and what the call leaves
(`call_ok`): the frame and its slots, as the original call does
(`AfterCall`), and, if `pre` holds the values for `n`, the result of the
public operation in `out`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Pc

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)

/-! ## The arguments -/

/-- A stack argument, past stores to the frame. -/
theorem arg_keep {s : State} (hp : PPre s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 8) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp.toEPre
  have := hp.sp3
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega_using [])) (by unfold frameBytes at *; omega_using [hj])

theorem arg_read {s t : State} (hp : PPre s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 8) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  rw [hrd]
  apply (Covers.one hp.args).left
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [stackArgAddr_eq s j]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- `pre` and `pre_len` in place of `n` and `n_len`. -/
theorem load_pre {s t : State} (hp : PPre s) (h : PreCall s t) :
    WP isa (.block [.mov .rdx (.mem (arg 6)), .mov .rcx (.mem (arg 7))]) t fun u =>
      Keep [.rdx, .rcx] t u ∧ u.mem = t.mem ∧ u.gpr .rdx = stackArg s 6 ∧ u.gpr .rcx = stackArg s 7 := by
  refine WP.keep [.rdx, .rcx] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  xrun [ea_arg (s := s), h.rsp, arg_read hp h.rd (show 6 < 8 by decide), arg_read hp h.rd (show 7 < 8 by decide),
    arg_keep hp h.out (show 6 < 8 by decide), arg_keep hp h.out (show 7 < 8 by decide)]

/-- Before the call, with its arguments in registers. -/
def J5 (s t : State) : Prop :=
  PreCall s t ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = stackArg s 6 ∧
    t.gpr .rcx = stackArg s 7 ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

theorem callArgs_ok {s t : State} (hp : PPre s) (h : PreCall s t) :
    WP isa (.block Impl.RsaPkcs1Enc.X86_64.Precomputed.callArgs) t fun u =>
      J5 s u ∧ Keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] t u := by
  unfold Impl.RsaPkcs1Enc.X86_64.Precomputed.callArgs
  rw [WP.block_append_iff]
  refine WP.mono (callArgs_run hp.toEPre h) fun t' ⟨hm, hdi, hsi, _, _, h8, h9, k⟩ => ?_
  have h' : PreCall s t' := ⟨(k.gpr (by decide)).trans h.rsp, k.2.1.trans h.rd,
    k.2.2.trans h.wr, hm ▸ h.out, hm ▸ h.slots, hm ▸ h.sZ, hm ▸ h.em⟩
  refine WP.mono (load_pre hp h') fun u ⟨k', hm', hdx, hcx⟩ => ?_
  exact ⟨⟨⟨(k'.gpr (by decide)).trans h'.rsp, k'.2.1.trans h'.rd, k'.2.2.trans h'.wr, hm' ▸ h'.out,
    hm' ▸ h'.slots, hm' ▸ h'.sZ, hm' ▸ h'.em⟩, (k'.gpr (by decide)).trans hdi, (k'.gpr (by decide)).trans hsi,
    hdx, hcx, (k'.gpr (by decide)).trans h8, (k'.gpr (by decide)).trans h9⟩, (k.trans k').mono (by decide)⟩

/-! ## The callee's view -/

/-- What `vg_rsa_public_precomputed_checked` reads: `pre`, `e`, `EM` and its
stack arguments. -/
def callRd (s : State) : List Region :=
  [preR s, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩, ⟨fb s, 32⟩]

theorem call_pre {s t : State} (hp : PPre s) (h : J5 s t) :
    Proof.Bignum.X86_64.pdContract.pre (t.callEntry.withRegions (callRd s) (pubWr s)) := by
  obtain ⟨h, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have e0 : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = off (fb s) oEM := by
    rw [stackArg_entry h.rsp _ _ (by decide)]
    have := h.slots.a0; simp only [Bignum.word, off_zero, Nat.mul_zero]; exact this
  have e1 : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 1 = s.gpr .rcx := by
    rw [stackArg_entry h.rsp _ _ (by decide)]; exact h.slots.a1
  have e2 : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 2 = stackArg s 4 := by
    rw [stackArg_entry h.rsp _ _ (by decide)]; exact h.slots.a2
  have e3 : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 3 = stackArg s 5 := by
    rw [stackArg_entry h.rsp _ _ (by decide)]; exact h.slots.a3
  simp only [pdContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, h.rsp,
    stackArgAddr_entry h.rsp, e0, e1, e2, e3, fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp.toEPre
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have e5 : encStack = 1120 := rfl
  have e6 : oEM = 80 := rfl
  have e7 : frameBytes = 1112 := rfl
  have hfb : fb s = off (kb s) 8 := fb_eq s
  have sM : Region.Sub ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ (stkR s) := frame_sub s (by omega_using [hk2, e6, e7])
  have sA : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 32) (by decide); simpa only [off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have dMA : (⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨fb s, 32⟩ :=
    Offset.disjoint_base _ (by decide) (by omega_using [hk2, e6])
  have dRM : (⟨kb s, 8⟩ : Region).Disjoint ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ := by
    rw [hfb, off_off]; exact Offset.base_disjoint _ (by decide) (by omega_using [hk2, e6])
  have dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega_using [])
  have wM : (off (fb s) oEM).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [hfb, off_off]; simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hK1, hk2, e5, e6]
  have dKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ := by have := hp.dKo; rwa [hsi'] at this
  have dOq : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (preR s) := by
    have := hp.preOut; rw [outR, hsi'] at this; exact this.symm
  have dOe : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ := by
    have := hp.dOe; rwa [hsi'] at this
  have dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ := by
    have := hp.dOs; rwa [hsi'] at this
  have wO : (s.gpr .rdi).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by have := hp.wO; omega_using [hsi', this]
  refine ⟨by omega_using [hK1], rfl, rfl, dOq, dOe, (dKo.sub_left sM).symm, dOs, (dKo.sub_left sA).symm, hp.preScr, hp.des,
    (hp.dKs.sub_left sM), (hp.dKs.sub_left sA).symm, dKo.sub_left sR, hp.preStack.symm.sub_left sR,
    hp.dKe.sub_left sR, dRM, hp.dKs.sub_left sR, dRA, wO, hp.preWrap, hp.wE, wM, hp.wS, ⟨hk1, hk2⟩, hp.preLen,
    trivial, hp.L1, hp.L2, hp.hsl⟩

theorem call_covers {s t : State} (hp : PPre s) (h : PreCall s t) :
    Covers (callRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  obtain ⟨-, cw⟩ := pub_covers hp.toEPre h
  have hk2 := hp.k2
  have e2 : oEM = 80 := rfl
  have e3 : frameBytes = 1112 := rfl
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  refine ⟨Covers.append_left ?_ cw.right, cw⟩
  have cr : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArgAddr s 0, 48⟩]
      (t.rd ++ t.wr) := by rw [h.rd]; exact hp.hrd.left
  apply Covers.of_forall
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.rd]; exact (Covers.one hp.pre).left
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_append_right _ hfr, oEM, rfl, by dsimp only; omega_using [hk2, e2, e3]⟩
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; omega_using [e3]⟩

/-- `pre`, unchanged where the function writes. -/
theorem pre_words {s : State} {m : Mem} (hp : PPre s) (hf : Frame [stkR s, outR s, scrR s] s.mem m) :
    Spec.Rsa.wordsAt m (stackArg s 6) (stackArg s 7).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  apply hf.readW (r := preR s) ?_ ?_ (by decide)
  · exact Offset.contains_base _ (by have := List.mem_range.mp hi; omega_using [this])
      (by have := hp.preWrap; have := List.mem_range.mp hi; omega_arith)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.preStack
    · exact hp.preOut
    · exact hp.preScr

/-- After the call: the frame, and the public operation's result if `pre`
holds the values for `n`. -/
structure PostCallP (s t : State) : Prop extends AfterCall s t where
  res : Spec.Rsa.publicPrecompute (nB s) = some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat) →
    Spec.Rsa.written t.mem (s.gpr .rdi) (kOf s) ((t.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOpChecked (nB s) (eB s) (Spec.RsaPkcs1Enc.encode (msgB s) (psB s)))

theorem call_ok (v : PublicImpl) {s t : State} (hp : PPre s) (hj : J5 s t) :
    WP isa (.call v.name v.code) t fun t' => PostCallP s t' ∧ (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hpre := call_pre hp hj
  obtain ⟨h, hdi, hsi, hdx, hcx, h8, h9⟩ := hj
  obtain ⟨hc, hw⟩ := call_covers hp h
  refine WP.call_mx (s := t) (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩) (rd := callRd s)
    (wr := pubWr s) v.ok v.nosp (by rw [v.depth]; decide) hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, h.rsp] at hf
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have e6 : oEM = 80 := rfl
  have e7 : frameBytes = 1112 := rfl
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call (frame_of_outside h.out) (callEntry_frame h.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (ret_sub s)
  have hE0 : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = off (fb s) oEM := by
    rw [stackArg_entry h.rsp _ _ (by decide)]
    have := h.slots.a0; simp only [Bignum.word, off_zero, Nat.mul_zero]; exact this
  have hem : Spec.Rsa.bytesAt t.callEntry.mem (off (fb s) oEM) (s.gpr .rcx).toNat =
      Spec.RsaPkcs1Enc.encode (msgB s) (psB s) := by
    rw [← h.em]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (callEntry_frame h.rsp).bytes (R := ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩)
      (fun r hr => ?_) (by show (s.gpr .rcx).toNat ≤ 2 ^ 64; omega_using []) (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr]
    exact slot_apart hp.toEPre (d := oEM) (n := (s.gpr .rcx).toNat) (by omega_using [hk2, e6, e7]) _
      (List.mem_append_right _ (List.mem_singleton_self _))
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hE0, hem, hm₂,
    hg₂ .rax (by decide)] at hpost
  rw [pre_words hp hfE,
    bytes_of_frame hfE hp.dKe (by have := hp.dOe; rw [outR]; exact this) hp.des.symm (by have := hp.wE; omega_using [])]
    at hpost
  have hkeep : ∀ {d : Nat}, d + 8 ≤ oEM → word s'.mem (fb s) d = word t.mem (fb s) d := fun hd =>
    hf.readW (Region.contains_self _ _) (slot_apart hp.toEPre (by omega_using [e6, e7, hd])) (by decide)
  have hkeep0 : s'.mem.readW (fb s) 64 = t.mem.readW (fb s) 64 := by
    have := hkeep (d := 0) (by decide); simp only [Bignum.word, off_zero] at this; exact this
  refine ⟨⟨⟨(hcs .rsp (by decide)).trans h.rsp, hrd.trans h.rd, hwr.trans h.wr,
    frame_call (frame_of_outside h.out) hf fun r hr => ?_,
    ⟨(hkeep (by decide)).trans h.slots.sOut, (hkeep (by decide)).trans h.slots.sN,
      (hkeep (by decide)).trans h.slots.sK, (hkeep (by decide)).trans h.slots.sE,
      (hkeep (by decide)).trans h.slots.sEl, hkeep0.trans h.slots.a0, (hkeep (by decide)).trans h.slots.a1,
      (hkeep (by decide)).trans h.slots.a2, (hkeep (by decide)).trans h.slots.a3⟩,
    (hkeep (by decide)).trans h.sZ⟩, fun hq => hpost _ (bytesAt_len ..) hq⟩, hcs, hmx⟩
  simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr (.inl (by rw [outR, hsi']; exact sub_refl _))
  · exact .inr (.inr (sub_refl _))
  · exact .inl (ret_sub s)

end VG.Proof.RsaPkcs1Enc.X86_64.Pc

end

end

/-! ### `RsaPkcs1Enc.X86_64.PcCorrect`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64: correctness

`EM` as `vg_rsa_pkcs1_encrypt` builds it (`em_ok`), the call with `pre`
(`callArgs_ok`, `call_ok`) and the mask (`tail_ok`): if `pre` holds the
values for `n`, `encK`'s postcondition (`code_correct`), and the frame and
the registers the ABI keeps whatever `pre` holds.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Pc

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-- `encK`'s postcondition, if `pre` holds the values for `n`. -/
def post (s u : State) : Prop :=
  Spec.Rsa.publicPrecompute (nB s) = some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat) →
    encK.post s u

theorem body_eq (pubName : String) (pub : Prog isa) :
    Impl.RsaPkcs1Enc.X86_64.Precomputed.body pubName pub = .seq (.block setup) (.seq psLoop (.seq (.block sep)
      (.seq msgCopy (.seq (.block Impl.RsaPkcs1Enc.X86_64.Precomputed.callArgs) (.seq (.call pubName pub)
        (.seq (.block maskArgs) (.seq maskLoop (.block [.mov .rax (.reg .r11)])))))))) :=
  rfl

theorem code_correct (v : PublicImpl) (s : State)
    (h : (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).pre s) :
    ∃ t s', Exec isa (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code) s t s' ∧ abiPreserved s s' ∧
      post s s' := by
  have hp := pre_of h
  suffices hw : WP isa (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code) s fun s' =>
      abiPreserved s s' ∧ post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine wp_alloc (by decide) (by decide) (by decide) (by have := hp.sp1; unfold encStack at this; omega_using [this]) ?_
  rw [body_eq]
  refine wp_seq4 (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r10, .r11] (em_ok hp.toEPre) (by decide +kernel))
    fun t ⟨hpc, k⟩ hmx => (⟨hpc, k, hmx⟩ : PreCall s t ∧ Keep _ (allocState frameBytes s) t ∧ _)) ?_
  intro t₁ ⟨hpc, k₁, hmx₁⟩
  refine WP.seq (WP.mono_mx (by decide +kernel) (callArgs_ok hp hpc) fun t₂ ⟨hj, k₂⟩ hmx₂ => ?_)
  refine WP.seq (WP.mono (call_ok v hp hj) fun t₃ ⟨hpost, hcs₃, hmx₃⟩ => ?_)
  refine WP.mono_mx (by decide +kernel) (tail_ok hp.toEPre hpost.toAfterCall) fun t₄ ht hmx₄ => ?_
  refine ⟨ht.rsp, by rw [ht.wr]; rfl, fun m u fm => ?_⟩
  have hs := VG.Proof.RsaPkcs1Enc.X86_64.frame_sub s (d := 0) (n := frameBytes) (by omega_using [])
  simp only [off, BitVec.add_zero] at hs
  refine ⟨⟨fun r hr => ?_, ret_frame hp.toEPre (ht.mem.trans (fm.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., hs⟩)), ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show t₄.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [ht.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else t₄.gpr r) = s.gpr r
      have hnr : r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [hr', ↓reduceIte]
      rw [ht.keep.gpr (not_mem_of hnr (by decide)), hcs₃ r hr, k₂.gpr (not_mem_of hnr (by decide)),
        k₁.gpr (not_mem_of hnr (by decide))]
      simp only [allocState_gpr, hr', ↓reduceIte]
  · show t₄.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [hmx₄, hmx₃, hmx₂, hmx₁]; rfl
  · intro hq
    have := result_ok hp.toEPre ⟨hpost.toAfterCall, hpost.res hq⟩ ht
    simp only [encK] at this ⊢
    have hsi := hp.toEPre.hsi
    exact Proof.Rsa.written_frame fm (s.gpr .rcx).isLt (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      have := (hp.toEPre.dKo.sub_left hs).symm
      rwa [hsi] at this) this

end VG.Proof.RsaPkcs1Enc.X86_64.Pc

end

end


/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64: the contract

`contract` is the shared contract's precondition, `post`, and `encK`'s public
data with `pre` and its words; it implies the shared contract (`implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

def contract : Contract isa where
  pre := (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).pre
  post := post
  pub a s := encK.pub a s ∧ stackArg a 6 = stackArg s 6 ∧ stackArg a 7 = stackArg s 7 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat

/-- `encSatState`, with 16 words of `pre` at `0x5000`. -/
def satState : State := { encSatState with
  mem := fun a => if a = 0x10039 then 0x50 else if a = 0x10040 then 16 else encSatState.mem a
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 61⟩, ⟨0x5000, 128⟩, ⟨0x10008, 64⟩] }

theorem implies : contract.Implies (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack) where
  pre := fun _ h => h
  post := by sig_implies_post [Proof.RsaPkcs1Enc.encryptPrecomputedContract,
    Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs, contract, post, encK, encStack,
    Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig,
      abi, argRegs, contract, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hcx, h9])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hb
    refine ⟨⟨?_, by simp only [stackArgs_six, a0, a1, a2, a3, a4, a5], hn, he⟩, a6, a7, hq'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Proof.RsaPkcs1Enc.encryptPrecomputedContract,
    Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs, contract, encStack,
    Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight, List.append_eq]
    [satState, encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.RsaPkcs1Enc.X86_64.Pc

end

end

/-! ### `RsaPkcs1Enc.X86_64.EncCT`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: constant time

Two runs from entry states that agree on the public data (`encK.pub`: the
pointers and lengths, `n` and `e`) leak the same trace. Each point of the
code is described, in each run, by what correctness says of it from that
run's entry state, which agrees with an anchor `a` on the public data
(`At`): the blocks and loops are checked by the taint analysis from the
registers this fixes (`PS`, the zero test and the mask are never among
them), the branch on the message's length agrees since the length is
public, and the call is constant time for its callee's contract, whose
public data it fixes too.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data.
The pieces of the code are proved for any relation `R` of an anchor to an
entry state that implies this one (`hR`), so that a variant of the function
with more public data (`PcCT`) uses them too. -/
def Sib (a s : State) : Prop := EPre s ∧ encK.pub a s

theorem pub_refl (s : State) : encK.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem Sib.arg {a s : State} (h : Sib a s) {i : Nat} (hi : i < 6) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.2.1) i (List.mem_range.mpr hi)).symm

theorem Sib.e {a s : State} (h : Sib a s) : eB s = eB a := h.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : Sib a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

/-- A point of a run, described by `J` from the run's entry state, which `R`
relates to the anchor. -/
def At (R J : State → State → Prop) (a t : State) : Prop := ∃ s, R a s ∧ J s t

/-- A register `J` gives as a function of the public data. -/
theorem pin {R J : State → State → Prop} (hR : ∀ a s, R a s → Sib a s) {r : Reg} (f : State → BitVec 64)
    (hf : ∀ s t, J s t → t.gpr r = f s) (hs : ∀ a s, Sib a s → f s = f a) {a t₁ t₂ : State}
    (h₁ : At R J a t₁) (h₂ : At R J a t₂) : t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ (hR _ _ S₁), hs _ _ (hR _ _ S₂)]

/-- Registers `J` gives as functions of the public data, at once. -/
theorem pins {R J : State → State → Prop} (hR : ∀ a s, R a s → Sib a s) (rs : List (Reg × (State → BitVec 64)))
    (hf : ∀ p ∈ rs, ∀ s t, J s t → t.gpr p.1 = p.2 s) (hs : ∀ p ∈ rs, ∀ a s, Sib a s → p.2 s = p.2 a) :
    Pins (At R J) (rs.map (·.1)) := fun a t₁ t₂ h₁ h₂ r hr => by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact pin hR p.2 (hf p hp) (hs p hp) h₁ h₂

theorem arg_pin {i : Nat} (hi : i < 6) : ∀ a s, Sib a s → stackArg s i = stackArg a i := fun _ _ h => h.arg hi

theorem fb_pin : ∀ a s, Sib a s → fb s = fb a := fun _ _ h => h.fb

theorem const_pin (v : BitVec 64) : ∀ a s, Sib a s → (fun _ : State => v) s = (fun _ : State => v) a :=
  fun _ _ _ => rfl

theorem gpr_pin {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    ∀ a s, Sib a s → s.gpr r = a.gpr r := fun _ _ h => h.gpr hr

/-! ## The pieces before the call -/

section
variable {R : State → State → Prop} (hR : ∀ a s, R a s → Sib a s)
include hR

def J0 (s t : State) : Prop := t = allocState frameBytes s

theorem setup_two : RelCT isa (Two (At R J0)) (.block setup) (Two (At R AfterSetup)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pin hR fb (fun s t h => by rw [h]; rfl) fb_pin h₁ h₂) (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by subst ht; exact WP.mono (setup_step (hR _ _ S).1) fun _ h => ⟨s, S, h⟩

theorem ps_two : RelCT isa (Two (At R AfterSetup)) psLoop (Two (At R AfterPs)) :=
  two_piece [.rsp, .rsi, .rcx, .r10] (pins (J := AfterSetup) hR [(.rsp, fb), (.rsi, fun s => stackArg s 2),
      (.rcx, fun s => stackArg s 3), (.r10, fun _ => BitVec.ofNat 64 0)] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl) s t h
        · exact h.keep.gpr (by decide)
        · exact h.rsi
        · exact h.rcx
        · exact h.r10) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl)
        · exact fb_pin
        · exact arg_pin (by decide)
        · exact arg_pin (by decide)
        · exact const_pin _)) (by taint_decide)
    fun _ _ ⟨s, S, h⟩ => WP.mono (ps_step (hR _ _ S).1 h) fun _ h => ⟨s, S, h⟩

theorem sep_two : RelCT isa (Two (At R AfterPs)) (.block sep) (Two (At R Mid)) :=
  two_piece [.rsp, .rcx] (pins (J := AfterPs) hR [(.rsp, fb), (.rcx, fun s => stackArg s 3)] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) s t h
        · exact h.rsp
        · exact h.rcx) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl)
        · exact fb_pin
        · exact arg_pin (by decide))) (by taint_decide)
    fun _ _ ⟨s, S, h⟩ => WP.mono (sep_step (hR _ _ S).1 h) fun _ h => ⟨s, S, h⟩

theorem copy_two : RelCT isa (Two (At R Mid)) msgCopy (Two (At R PreCall)) := by
  refine two_ite (fun _ t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
    rw [eval_ne_mid h₁, eval_ne_mid h₂, (hR _ _ S₁).arg (by decide), (hR _ _ S₂).arg (by decide)]) ?_ ?_
  · refine two_piece [.rsp, .rdi, .rsi, .rcx, .r10] (fun a t₁ t₂ ⟨⟨s₁, S₁, h₁⟩, _⟩ ⟨⟨s₂, S₂, h₂⟩, _⟩ r hr => ?_)
      (by taint_decide) fun _ _ ⟨⟨s, S, h⟩, hc⟩ => WP.mono (msgLoop_step (hR _ _ S).1 h ?_) fun _ h => ⟨s, S, h⟩
    · have S₁ := hR _ _ S₁
      have S₂ := hR _ _ S₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.rsp, h₂.rsp, S₁.fb, S₂.fb]
      · rw [h₁.rdi, h₂.rdi, S₁.fb, S₂.fb, S₁.arg (by decide), S₂.arg (by decide)]
      · rw [h₁.rsi, h₂.rsi, S₁.arg (by decide), S₂.arg (by decide)]
      · rw [h₁.rcx, h₂.rcx, S₁.arg (by decide), S₂.arg (by decide)]
      · rw [h₁.r10, h₂.r10]
    · rw [eval_ne_mid h] at hc
      simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at hc
      exact Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq (by simp [h]))
  · refine two_piece [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
      fun _ _ ⟨⟨s, S, h⟩, hc⟩ => WP.block_nil ⟨s, S, empty_step (hR _ _ S).1 h ?_⟩
    rw [eval_ne_mid h] at hc
    simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_false, beq_iff_eq] at hc
    rw [hc]; rfl

/-! ## The mask -/

def J7 (s t : State) : Prop :=
  t.gpr .rsp = fb s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r10 = BitVec.ofNat 64 0

theorem maskArgs_two : RelCT isa (Two (At R AfterCall)) (.block maskArgs) (Two (At R J7)) :=
  two_piece [.rsp] (pins (J := AfterCall) hR [(.rsp, fb)] (by
        simp only [List.mem_singleton]; rintro p rfl s t h; exact h.rsp) (by
        simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun _ _ ⟨s, S, h⟩ => WP.mono (maskArgs_run (hR _ _ S).1 h)
      fun _ ⟨_, _, _, hdi, hcx, h10, k⟩ => ⟨s, S, (k.gpr (by decide)).trans h.rsp, hdi, hcx, h10⟩

theorem mask_ct : RelCT isa (Two (At R J7)) (.seq maskLoop (.block [.mov .rax (.reg .r11)])) fun _ _ => True :=
  two_taint [.rsp, .rdi, .rcx, .r10] (pins (J := J7) hR [(.rsp, fb), (.rdi, fun s => s.gpr .rdi),
      (.rcx, fun s => s.gpr .rcx), (.r10, fun _ => BitVec.ofNat 64 0)] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl) s t h
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl)
        · exact fb_pin
        · exact gpr_pin (by decide)
        · exact gpr_pin (by decide)
        · exact const_pin _)) (by taint_decide)

end

/-! ## The call -/

/-- The registers a callee sees, from the caller's. -/
theorem entry_regs (t : State) (rd wr : List Region) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions rd wr).gpr =
      [t.gpr .rdi, t.gpr .rsi, t.gpr .rdx, t.gpr .rcx, t.gpr .r8, t.gpr .r9, t.gpr .rsp - 8] := by
  simp only [List.map_cons, List.map_nil, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]

theorem regs_eq {s₁ s₂ : State}
    (h : [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₁.gpr = [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₂.gpr) :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp h

/-- A caller's buffer, read by the callee: the same as at the entry. -/
theorem entryBytes {s t : State} (h : PreCall s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  rw [State.withRegions_mem]
  exact bytes_of_frame (frame_call (frame_of_outside h.out) (callEntry_frame h.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (ret_sub s)) hk ho hs hl

end VG.Proof.RsaPkcs1Enc.X86_64

end

end

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64: constant time

The pieces of `vg_rsa_pkcs1_encrypt` (`EncCT`), for entry states related to
the anchor by `contract` (`PR`), and the call of the precomputed public
operation, constant time for its contract, which makes `pre`'s words public
too. Nothing after the call branches on its result.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.PcCT

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open Pc

/-- An entry state meeting the precondition with the anchor's public data. -/
def PR (a s : State) : Prop := contract.pre s ∧ contract.pub a s

theorem pr_sib : ∀ a s, PR a s → Sib a s := fun _ _ h => ⟨(pre_of h.1).toEPre, h.2.1⟩

theorem pub_refl (s : State) : contract.pub s s := ⟨X86_64.pub_refl s, rfl, rfl, rfl⟩

theorem callArgs_two : RelCT isa (Two (At PR PreCall)) (.block Impl.RsaPkcs1Enc.X86_64.Precomputed.callArgs)
    (Two (At PR Pc.J5)) :=
  two_piece [.rsp] (pins (J := PreCall) pr_sib [(.rsp, fb)] (by
        simp only [List.mem_singleton]; rintro p rfl s t h; exact h.rsp) (by
        simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun _ _ ⟨s, S, h⟩ => WP.mono (callArgs_ok (pre_of S.1) h) fun _ hh => ⟨s, S, hh.1⟩

/-- What the precomputed public operation's contract makes public. -/
theorem pub_view {a s t : State} (S : PR a s) (h : Pc.J5 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (callRd s) (pubWr s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, stackArg a 6, stackArg a 7, a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = off (fb a) oEM ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 2 = stackArg a 4 ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 3 = stackArg a 5 ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r9).toNat = eB a := by
  obtain ⟨hpc, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := pre_of S.1
  have S' := pr_sib _ _ S
  have rcx := S'.gpr (r := .rcx) (by decide)
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call (frame_of_outside hpc.out) (callEntry_frame hpc.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (ret_sub s)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, hpc.rsp, S'.fb, rcx, S'.gpr (r := .rdi) (by decide),
      S.2.2.1, S.2.2.2.1, S'.gpr (r := .r8) (by decide), S'.gpr (r := .r9) (by decide)]
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← S'.fb]
    have := hpc.slots.a0; simp only [Bignum.word, off_zero, Nat.mul_zero]; exact this
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← rcx]; exact hpc.slots.a1
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← S'.arg (by decide)]; exact hpc.slots.a2
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← S'.arg (by decide)]; exact hpc.slots.a3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [State.withRegions_mem, pre_words hp hfE, S.2.2.2.2]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [entryBytes hpc _ _ hp.dKe (by have := hp.dOe; rw [outR]; exact this) hp.des.symm
      (by have := hp.wE; omega_using [])]
    exact S'.e

theorem call_ct (v : PublicImpl) : RelCT isa (Two (At PR Pc.J5)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pdChkContract) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, n₁, e₁⟩ := pub_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, n₂, e₂⟩ := pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := call_covers (pre_of S₁.1) j₁.1
  obtain ⟨c₂, w₂⟩ := call_covers (pre_of S₂.1) j₂.1
  have hpub : pdChkContract.pub (t₁.callEntry.withRegions (callRd s₁) (pubWr s₁))
      (t₂.callEntry.withRegions (callRd s₂) (pubWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩
  have p₁ := call_pre (pre_of S₁.1) j₁
  have p₂ := call_pre (pre_of S₂.1) j₂
  exact ⟨callRd s₁, pubWr s₁, callRd s₂, pubWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, by rw [j₁.1.rsp, j₂.1.rsp, (pr_sib _ _ S₁).fb, (pr_sib _ _ S₂).fb]⟩

theorem call_two (v : PublicImpl) : RelCT isa (Two (At PR Pc.J5)) (.call v.name v.code) (Two (At PR AfterCall)) :=
  two_post (call_ct v) fun _ _ ⟨s, S, h⟩ =>
    WP.mono (call_ok v (pre_of S.1) h) fun _ h => ⟨s, S, h.1.toAfterCall⟩

theorem body_ct (v : PublicImpl) : RelCT isa (Two (At PR J0))
    (Impl.RsaPkcs1Enc.X86_64.Precomputed.body v.name v.code) fun _ _ => True := by
  rw [Pc.body_eq]
  exact RelCT.seq (setup_two pr_sib) (RelCT.seq (ps_two pr_sib) (RelCT.seq (sep_two pr_sib)
    (RelCT.seq (copy_two pr_sib) (RelCT.seq callArgs_two (RelCT.seq (call_two v)
      (RelCT.seq (maskArgs_two pr_sib) (mask_ct pr_sib)))))))

theorem code_constantTime (v : PublicImpl) :
    ConstantTime isa contract.pre contract.pub (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code) :=
  RelCT.constantTime (relCT_alloc ((body_ct v).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, e₁⟩, ⟨s₂, ⟨h₂, hpub⟩, e₂⟩⟩)
    fun _ _ h => h))

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_encrypt_precomputed`, calling the implementation `v` of
`vg_rsa_public_precomputed_checked`, meets the shared contract. -/
theorem code_verified (v : PublicImpl) :
    Verified target (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code)
      (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack) :=
  Verified.of_correct (k := contract) (code_correct v) (code_constantTime v) implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : PublicImpl) :
    (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.RsaPkcs1Enc.X86_64.Precomputed.code, Impl.RsaPkcs1Enc.X86_64.Precomputed.body, Code.all,
    v.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Enc.X86_64.PcCT
