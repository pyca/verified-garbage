module

public import VerifiedGarbage.Proof.AesGcm.X86.CtrCall
public import VerifiedGarbage.Proof.AesGcm.X86.Common
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.X86.Common
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.Sm4Gcm.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.Proof.Gcm.X86.Ghash
public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Impl.Sm4Gcm.X86
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Sm4.X86.Ctr32
public import VerifiedGarbage.Impl.Sm4.X86.ExpandKey
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Gcm
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.X86.Ctr32Verified
import VerifiedGarbage.Proof.Sm4.X86.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.X86.KeyVerified
import VerifiedGarbage.Proof.Sm4.X86.Lit

/-! ### `Sm4Gcm.X86.Callee`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on x86: the calls

Untrusted: everything here is checked by Lean. Each call of `vg_sm4_ctr32`
and `vg_sm4_expand_key`, in a frame of its arguments, from the callee's
contract (`WP.callWith`): what it needs of the registers it pushes and of
the regions it is given (`CtrCall`, `KeyCall`), and what it leaves
(`CtrPost`, `KeyPost`), in terms of the memory before the call; and that it
is constant time (`ctr_ct`, `key_ct`) by the callee's own proof, when the
arguments are the same in both runs. They keep their working space on the
stack, and are called by their shared contracts (`Proof.Sm4.ctr32Contract`
with 1516 bytes of stack, `Spec.Sm4.expandKeyContract` with 1448), from the
layout the call gives them. The calls of `vg_ghash` are AES-GCM's
(`Proof/AesGcm/X86/Callee.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.Impl.Sm4Gcm.X86 VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 (Fn)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32)

/-! ## Stack layout below a call -/

theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- The bytes `[d, d + n)` of the `b` bytes below `E`, from their bottom. -/
theorem below_off {E : BitVec 32} {b d k : Nat} (hb : b ≤ E.toNat) (hk : k ≤ b) (hd : d = b - k) :
    ((E - BitVec.ofNat 32 k).setWidth 64) = (below E b).base + BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  have := E.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [sub_toNat (by omega_using [hb, hk]), sub_toNat hb]
  subst hd
  rw [Nat.mod_eq_of_lt (a := E.toNat - k) (by omega_using []), Nat.mod_eq_of_lt (a := E.toNat - b) (by omega_using []),
    Nat.mod_eq_of_lt (a := b - k) (by omega_using [hb]), Nat.mod_eq_of_lt (by omega_using [hb])]
  omega_using [hb, hk]

/-! ## `vg_sm4_ctr32` -/

abbrev ctrRegs : List Reg := [.edi, .ebx, .edx, .eax]

theorem ctrRegs_esp : Reg.esp ∉ ctrRegs := by decide

theorem ctr_stack : stackUse ctrFn.code = 1516 := by
  have h : stackUse Impl.Sm4.X86.ctr32 = 20 := by lit_decide
  simp only [ctrFn, Impl.StackScratch.X86.withStackScratchWiped, Impl.StackScratch.X86.withStackScratch,
    stackUse, h, X86.frameBytes]
  decide

theorem ctr_stack' :
    stackUse (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ctr32) = 1516 := ctr_stack

theorem ctr_nosp : NoSp ctrFn.code := NoSp.of_all (by unfold ctrFn; lit_decide)

theorem ctr_spSafe : ctrFn.code.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_spTest (by unfold ctrFn; lit_decide)

/-- What a call of `vg_sm4_ctr32` needs: the key schedule at `K`, the
counter block at `C` and `n` blocks at `D`, and 1536 bytes of stack for the
arguments, the return address and the callee's frames. -/
structure CtrCall (s : State) (K C D : BitVec 32) (n : Nat) : Prop where
  eax : s.gpr .eax = K
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  edi : s.gpr .edi = BitVec.ofNat 32 n
  esp : 1536 ≤ (s.gpr .esp).toNat
  kc : (⟨w64 K, 128⟩ : Region).Disjoint ⟨w64 C, 16⟩
  kd : (⟨w64 K, 128⟩ : Region).Disjoint ⟨w64 D, 16 * n⟩
  cd : (⟨w64 C, 16⟩ : Region).Disjoint ⟨w64 D, 16 * n⟩
  bk : (below (s.gpr .esp) 1536).Disjoint ⟨w64 K, 128⟩
  bc : (below (s.gpr .esp) 1536).Disjoint ⟨w64 C, 16⟩
  bd : (below (s.gpr .esp) 1536).Disjoint ⟨w64 D, 16 * n⟩
  fK : K.toNat + 128 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  reads : Covers [⟨w64 K, 128⟩] (s.rd ++ s.wr)
  writes : Covers [⟨w64 C, 16⟩, ⟨w64 D, 16 * n⟩] s.wr

/-- What a call of `vg_sm4_ctr32` leaves. -/
structure CtrPost (s : State) (K C D : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨w64 C, 16⟩, ⟨w64 D, 16 * n⟩, below (s.gpr .esp) 1536] s.mem s'.mem
  out : blocksAt s'.mem (w64 D) n = ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem (w64 K)))
    (blockAt s.mem (w64 C)) (blocksAt s.mem (w64 D) n)
  ctr : blockAt s'.mem (w64 C) = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem (w64 C))

abbrev ctrRd (K : BitVec 32) : List Region := [⟨w64 K, 128⟩]
abbrev ctrWr (E C D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 C, 16⟩, ⟨w64 D, n * 16⟩, below E 16]

/-- The contract `vg_sm4_ctr32` is called by. -/
abbrev ctrK : Contract isa := Proof.Sm4.ctr32Contract X86.abi 1516

namespace CtrCall
variable {s : State} {K C D : BitVec 32} {n : Nat} (h : CtrCall s K C D n)
include h

theorem fit : 4 * ctrRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega_using [this]

theorem n_lt : n < 2 ^ 32 := by have := h.fD; omega_using [this]

theorem args : arg (pushed ctrRegs s).callEntry 0 = K ∧ arg (pushed ctrRegs s).callEntry 1 = C ∧
    arg (pushed ctrRegs s).callEntry 2 = D ∧ arg (pushed ctrRegs s).callEntry 3 = BitVec.ofNat 32 n := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit ctrRegs_esp (by decide)] <;> simp [h.eax, h.edx, h.ebx, h.edi]

theorem callPre : CallPre ctrK ctrRegs (ctrRd K) (ctrWr (s.gpr .esp) C D n) s := by
  obtain ⟨a0, a1, a2, a3⟩ := h.args
  have hn := toNat_ofNat32 h.n_lt
  have hE := h.esp
  have := (s.gpr .esp).isLt
  have eA : argAddr (pushed ctrRegs s).callEntry 0 = (below (s.gpr .esp) 1536).base + BitVec.ofNat 64 1520 := by
    rw [callEntry_argAddr0]; exact below_off (by omega_using [hE]) (by decide) rfl
  have eB : (below (s.gpr .esp) 16) = ⟨(below (s.gpr .esp) 1536).base + BitVec.ofNat 64 1520, 16⟩ :=
    congrArg (fun x => (⟨x, 16⟩ : Region)) (below_off (by omega_using [hE]) (by decide) rfl)
  have e5 : s.gpr .esp - 4 - 4 - 4 - 4 - 4 = s.gpr .esp - BitVec.ofNat 32 20 := by
    simp only [BitVec.sub_sub]; rfl
  have eR : w64 (s.gpr .esp - BitVec.ofNat 32 20) = (below (s.gpr .esp) 1536).base + BitVec.ofNat 64 1516 :=
    below_off (by omega_using [hE]) (by decide) rfl
  have eS : (below (s.gpr .esp) 1536).base + BitVec.ofNat 64 1516 - 1516#64 = (below (s.gpr .esp) 1536).base :=
    BitVec.add_sub_cancel _ _
  have eN : (s.gpr .esp - BitVec.ofNat 32 20).toNat = (s.gpr .esp).toNat - 20 := sub_toNat (by omega_using [hE])
  let B := (below (s.gpr .esp) 1536).base
  try rewrite [show (below (s.gpr .esp) 1536).base = B from rfl] at *
  have hb : below (s.gpr .esp) 1536 = ⟨B, 1536⟩ := rfl
  have sb {d k : Nat} (hd : d + k ≤ 1536) {r : Region} (hr : (below (s.gpr .esp) 1536).Disjoint r) :
      (⟨B + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    rw [hb] at hr; exact hr.sub_left (Offset.sub_base _ hd)
  have sb0 {r : Region} (hr : (below (s.gpr .esp) 1536).Disjoint r) : (⟨B, 1516⟩ : Region).Disjoint r := by
    rw [hb] at hr; exact hr.sub_left (Region.sub_prefix (by decide))
  have hkd := h.kd
  have hcd := h.cd
  have hbd := h.bd
  have hfD := h.fD
  rw [Nat.mul_comm] at hkd hcd hbd hfD
  refine ⟨?_, ?_, ?_⟩
  · sig_pre [ctrK, Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, X86.abi, argVal, ↓reduceIte,
      Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
      toNat_w64]
    simp only [State.withRegions_rd, State.withRegions_wr, arg_withRegions, argAddr_withRegions, a0, a1, a2,
      a3, hn, eA, e5, eN, eR, eS]
    have r1 : (⟨B + BitVec.ofNat 64 1516, 4⟩ : Region).Disjoint ⟨B + BitVec.ofNat 64 1520, 16⟩ :=
      Offset.disjoint B (.inl (by decide)) (by omega_using []) (by omega_using [])
    have r2 : (⟨B, 1516⟩ : Region).Disjoint ⟨B + BitVec.ofNat 64 1520, 16⟩ :=
      Offset.base_disjoint B (by decide) (by omega_using [])
    refine ⟨by omega_using [hE], by omega_using [], trivial, by rw [ctrWr, eB], h.kc, hkd, (sb (by decide) h.bk).symm, hcd,
      (sb (by decide) h.bc).symm, (sb (by decide) hbd).symm, sb (by decide) h.bk, sb (by decide) h.bc,
      sb (by decide) hbd, r1, sb0 h.bk, sb0 h.bc, sb0 hbd, r2, h.fK, h.fC, hfD⟩
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨⟨w64 D, 16 * n⟩, by simp, by rwa [Nat.mul_comm]⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
    · obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨⟨w64 D, 16 * n⟩, by simp, by rwa [Nat.mul_comm]⟩
      exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
    · exact ⟨_, List.mem_cons_self .., hcn⟩

end CtrCall

/-- `vg_sm4_ctr32`'s postcondition. -/
theorem ctrK_post {s s' : State} (h : ctrK.post s s') :
    blocksAt s'.mem (w64 (arg s 2)) (arg s 3).toNat =
        ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem (w64 (arg s 0))))
          (blockAt s.mem (w64 (arg s 1))) (blocksAt s.mem (w64 (arg s 2)) (arg s 3).toNat) ∧
      blockAt s'.mem (w64 (arg s 1)) = Nat.repeat Spec.Gcm.inc32 (arg s 3).toNat (blockAt s.mem (w64 (arg s 1))) := by
  sig_post [ctrK, Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64] at h
  exact h

/-- Its public data, from the arguments. -/
theorem ctrK_pub {s₁ s₂ : State} (h : s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i) :
    ctrK.pub s₁ s₂ := by
  obtain ⟨a₁, a₂⟩ := h
  sig_pub [ctrK, Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, X86.abi, argVal, ↓reduceIte, Nat.reduceEqDiff,
    argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32, toNat_w64]
  exact ⟨a₁, a₂ 0 (by decide), a₂ 1 (by decide), a₂ 2 (by decide), a₂ 3 (by decide)⟩

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 128⟩ : Region).Disjoint r) : Spec.Sm4.scheduleAt m' p = Spec.Sm4.scheduleAt m p :=
  Proof.Sm4.scheduleAt_congr fun i hi => hf.bytes (R := ⟨p, 128⟩) hd (by show 128 ≤ 2 ^ 64; omega_using []) hi

theorem ctr_call {s : State} {K C D : BitVec 32} {n : Nat} (h : CtrCall s K C D n) :
    WP isa (ctrCall) s (CtrPost s K C D n) := by
  have hn := toNat_ofNat32 h.n_lt
  unfold ctrCall
  refine WP.callWith (rs := ctrRegs) (k := ctrK) Proof.Sm4.X86.Ctr32.ctr32_framed.1 ctr_nosp (by simp)
    ctrRegs_esp (by rw [ctr_stack']; have := h.esp
                    simp only [List.length_cons, List.length_nil]; omega_using [this])
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3⟩ := h.args
  rw [ctr_stack'] at f'
  have fE := callEntry_frame h.fit ctrRegs_esp
  rw [show 4 * ctrRegs.length + 4 = 20 from rfl] at fE
  have fE' : Frame [below (s.gpr .esp) 1536] s.mem (pushed ctrRegs s).callEntry.mem :=
    fE.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, VG.X86.below_sub (by decide) h.esp⟩
  obtain ⟨hdata, hctr⟩ := ctrK_post post
  simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, hn] at hdata hctr
  -- The pop loses the arguments' frame, below `esp`, apart from the buffers.
  have fL : Frame [below (s.gpr .esp) 1536] s₂.mem s'.mem := Frame.below_mono (wr := []) m₂ (by decide) h.esp
  rw [← blocksAt_frame fL (one_disj h.bd) (by have := h.fD; omega_using [hn])] at hdata
  rw [← blockAt_frame fL (one_disj h.bc)] at hctr
  rw [blockAt_frame fE' (one_disj h.bc), blocksAt_frame fE' (one_disj h.bd) (by have := h.fD; omega_using [hn]),
    scheduleAt_frame fE' (one_disj h.bk)] at hdata
  rw [blockAt_frame fE' (one_disj h.bc)] at hctr
  refine ⟨rd', wr', cs', ?_, hdata, hctr⟩
  refine f'.sub fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨⟨w64 D, 16 * n⟩, by simp, by rw [Nat.mul_comm]; exact fun _ h => h⟩
  · exact ⟨below (s.gpr .esp) 1536, by simp, VG.X86.below_sub (by decide) h.esp⟩
  · exact ⟨below (s.gpr .esp) 1536, by simp, VG.X86.below_sub (by decide) h.esp⟩

/-- Calls of `vg_sm4_ctr32` with the same arguments and stack pointer in
both runs are constant time. -/
theorem ctr_ct {I : State → Prop} {K C D E : BitVec 32} {n : Nat}
    (h : ∀ s, I s → CtrCall s K C D n ∧ s.gpr .esp = E) : CT I (ctrCall) := by
  refine CT.callWith Proof.Sm4.X86.Ctr32.ctr32_framed.1 Proof.Sm4.X86.Ctr32.ctr32_framed.2.1 (ctrRd K)
    (ctrWr E C D n) fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ctrK_pub ⟨?_, fun i hi => ?_⟩⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂]
  obtain ⟨a0, a1, a2, a3⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3⟩ := h₂.args
  simp only [arg_withRegions]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]

/-! ## `vg_sm4_expand_key` -/

abbrev keyRegs : List Reg := [.edx, .eax]

theorem keyRegs_esp : Reg.esp ∉ keyRegs := by decide

theorem key_stack' :
    stackUse (Impl.StackScratch.X86.withStackScratchWiped 1448 2 358 Impl.Sm4.X86.expandKey) = 1448 := by
  have h : stackUse Impl.Sm4.X86.expandKey = 0 := by lit_decide
  simp only [Impl.StackScratch.X86.withStackScratchWiped, Impl.StackScratch.X86.withStackScratch,
    stackUse, h, X86.frameBytes]
  decide

theorem key_nosp : NoSp keyFn.code := NoSp.of_all (by unfold keyFn; lit_decide)

theorem key_spSafe : keyFn.code.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_spTest (by unfold keyFn; lit_decide)

/-- What a call of `vg_sm4_expand_key` needs: the 16-byte key at `K` and the
key schedule at `C`, and 1460 bytes of stack for the arguments, the return
address and the callee's frames. -/
structure KeyCall (s : State) (K C : BitVec 32) : Prop where
  eax : s.gpr .eax = K
  edx : s.gpr .edx = C
  esp : 1460 ≤ (s.gpr .esp).toNat
  kc : (⟨w64 K, 16⟩ : Region).Disjoint ⟨w64 C, 128⟩
  bk : (below (s.gpr .esp) 1460).Disjoint ⟨w64 K, 16⟩
  bc : (below (s.gpr .esp) 1460).Disjoint ⟨w64 C, 128⟩
  fK : K.toNat + 16 ≤ 2 ^ 32
  fC : C.toNat + 128 ≤ 2 ^ 32
  reads : Covers [⟨w64 K, 16⟩] (s.rd ++ s.wr)
  writes : Covers [⟨w64 C, 128⟩] s.wr

/-- What a call of `vg_sm4_expand_key` leaves. -/
structure KeyPost (s : State) (K C : BitVec 32) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨w64 C, 128⟩, below (s.gpr .esp) 1460] s.mem s'.mem
  out : Spec.Sm4.scheduleAt s'.mem (w64 C) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (w64 K))

abbrev keyRd (E K : BitVec 32) : List Region := [⟨w64 K, 16⟩, below E 8]
abbrev keyWr (C : BitVec 32) : List Region := [⟨w64 C, 128⟩]

/-- The contract `vg_sm4_expand_key` is called by. -/
abbrev keyK : Contract isa := Spec.Sm4.expandKeyContract X86.abi 1448

namespace KeyCall
variable {s : State} {K C : BitVec 32} (h : KeyCall s K C)
include h

theorem fit : 4 * keyRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega_using [this]

theorem args : arg (pushed keyRegs s).callEntry 0 = K ∧ arg (pushed keyRegs s).callEntry 1 = C := by
  refine ⟨?_, ?_⟩ <;>
  rw [callEntry_arg h.fit keyRegs_esp (by decide)] <;> simp [h.eax, h.edx]

theorem callPre : CallPre keyK keyRegs (keyRd (s.gpr .esp) K) (keyWr C) s := by
  obtain ⟨a0, a1⟩ := h.args
  have hE := h.esp
  have := (s.gpr .esp).isLt
  have eA : argAddr (pushed keyRegs s).callEntry 0 = (below (s.gpr .esp) 1460).base + BitVec.ofNat 64 1452 := by
    rw [callEntry_argAddr0]; exact below_off (by omega_using [hE]) (by decide) rfl
  have eB : (below (s.gpr .esp) 8) = ⟨(below (s.gpr .esp) 1460).base + BitVec.ofNat 64 1452, 8⟩ :=
    congrArg (fun x => (⟨x, 8⟩ : Region)) (below_off (by omega_using [hE]) (by decide) rfl)
  have e3 : s.gpr .esp - 4 - 4 - 4 = s.gpr .esp - BitVec.ofNat 32 12 := by
    simp only [BitVec.sub_sub]; rfl
  have eR : w64 (s.gpr .esp - BitVec.ofNat 32 12) = (below (s.gpr .esp) 1460).base + BitVec.ofNat 64 1448 :=
    below_off (by omega_using [hE]) (by decide) rfl
  have eS : (below (s.gpr .esp) 1460).base + BitVec.ofNat 64 1448 - 1448#64 = (below (s.gpr .esp) 1460).base :=
    BitVec.add_sub_cancel _ _
  have eN : (s.gpr .esp - BitVec.ofNat 32 12).toNat = (s.gpr .esp).toNat - 12 := sub_toNat (by omega_using [hE])
  let B := (below (s.gpr .esp) 1460).base
  try rewrite [show (below (s.gpr .esp) 1460).base = B from rfl] at *
  have hb : below (s.gpr .esp) 1460 = ⟨B, 1460⟩ := rfl
  have sb {d k : Nat} (hd : d + k ≤ 1460) {r : Region} (hr : (below (s.gpr .esp) 1460).Disjoint r) :
      (⟨B + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    rw [hb] at hr; exact hr.sub_left (Offset.sub_base _ hd)
  have sb0 {r : Region} (hr : (below (s.gpr .esp) 1460).Disjoint r) : (⟨B, 1448⟩ : Region).Disjoint r := by
    rw [hb] at hr; exact hr.sub_left (Region.sub_prefix (by decide))
  have r1 : (⟨B + BitVec.ofNat 64 1448, 4⟩ : Region).Disjoint ⟨B + BitVec.ofNat 64 1452, 8⟩ :=
    Offset.disjoint B (.inl (by decide)) (by omega_using []) (by omega_using [])
  have r2 : (⟨B, 1448⟩ : Region).Disjoint ⟨B + BitVec.ofNat 64 1452, 8⟩ :=
    Offset.base_disjoint B (by decide) (by omega_using [])
  refine ⟨?_, ?_, ?_⟩
  · sig_pre [keyK, Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86.abi, argVal, ↓reduceIte,
      Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
      toNat_w64]
    simp only [State.withRegions_rd, State.withRegions_wr, arg_withRegions, argAddr_withRegions, a0, a1,
      eA, e3, eN, eR, eS]
    refine ⟨by omega_using [hE], by omega_using [], by rw [keyRd, eB], trivial, h.kc, (sb (by decide) h.bc).symm,
      sb (by decide) h.bk, sb (by decide) h.bc, r1, sb0 h.bk, sb0 h.bc, r2, h.fK, h.fC⟩
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    · obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a m hi
    obtain ⟨r', hr', hc'⟩ := h.writes a m hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end KeyCall

/-- `vg_sm4_expand_key`'s postcondition. -/
theorem keyK_post {s s' : State} (h : keyK.post s s') :
    Spec.Sm4.scheduleAt s'.mem (w64 (arg s 1)) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (w64 (arg s 0))) := by
  sig_post [keyK, Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64] at h
  exact h

/-- Its public data, from the arguments. -/
theorem keyK_pub {s₁ s₂ : State} (h : s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 2, arg s₁ i = arg s₂ i) :
    keyK.pub s₁ s₂ := by
  obtain ⟨a₁, a₂⟩ := h
  sig_pub [keyK, Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64]
  exact ⟨a₁, a₂ 0 (by decide), a₂ 1 (by decide)⟩

theorem sm4BlockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : Spec.Sm4.blockAt m' p = Spec.Sm4.blockAt m p := by
  apply Vector.ext; intro i hi
  simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 16⟩) hd (by show 16 ≤ 2 ^ 64; omega_using []) hi

theorem key_call {s : State} {K C : BitVec 32} (h : KeyCall s K C) :
    WP isa (keyCall) s (KeyPost s K C) := by
  unfold keyCall
  refine WP.callWith (rs := keyRegs) (k := keyK) Proof.Sm4.X86.expandKey_framed.1 key_nosp (by simp)
    keyRegs_esp (by rw [key_stack']; have := h.esp
                    simp only [List.length_cons, List.length_nil]; omega_using [this])
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1⟩ := h.args
  rw [key_stack'] at f'
  have fE := callEntry_frame h.fit keyRegs_esp
  rw [show 4 * keyRegs.length + 4 = 12 from rfl] at fE
  have fE' : Frame [below (s.gpr .esp) 1460] s.mem (pushed keyRegs s).callEntry.mem :=
    fE.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, VG.X86.below_sub (by decide) h.esp⟩
  have hout := keyK_post post
  simp only [arg_withRegions, State.withRegions_mem, a0, a1] at hout
  -- The pop loses the arguments' frame, below `esp`, apart from the schedule.
  have fL : Frame [below (s.gpr .esp) 1460] s₂.mem s'.mem := Frame.below_mono (wr := []) m₂ (by decide) h.esp
  rw [← scheduleAt_frame fL (one_disj h.bc)] at hout
  rw [sm4BlockAt_frame fE' (one_disj h.bk)] at hout
  refine ⟨rd', wr', cs', ?_, hout⟩
  refine f'.sub fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨below (s.gpr .esp) 1460, by simp, VG.X86.below_sub (by decide) h.esp⟩

/-- Calls of `vg_sm4_expand_key` with the same arguments and stack pointer in
both runs are constant time. -/
theorem key_ct {I : State → Prop} {K C E : BitVec 32}
    (h : ∀ s, I s → KeyCall s K C ∧ s.gpr .esp = E) : CT I (keyCall) := by
  refine CT.callWith Proof.Sm4.X86.expandKey_framed.1 Proof.Sm4.X86.expandKey_framed.2.1 (keyRd E K)
    (keyWr C) fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, keyK_pub ⟨?_, fun i hi => ?_⟩⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂]
  obtain ⟨a0, a1⟩ := h₁.args
  obtain ⟨b0, b1⟩ := h₂.args
  simp only [arg_withRegions]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]

end VG.Proof.Sm4Gcm.X86

end

end

/-! ### `Sm4Gcm.X86.Lay`, which only this module used -/

section

/-!
# SM4-GCM on x86: the stack the calls use

Untrusted: everything here is checked by Lean. SM4-GCM's functions share
AES-GCM's layout (`Proof/AesGcm/X86/Env.lean`): its pieces that only hash
or compare run with `Lay Ctx St W SP 28`, the 28 bytes below `SP` its
calls use. A call of `vg_sm4_ctr32` uses `K` (1536) bytes below `SP`, apart
from the context, the state and `W` too (`Lay4`); what a piece of AES-GCM
leaves below `SP` is within them (`Lay4.below28`), and data apart from them
is apart from AES-GCM's (`DataOk.mono`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.Proof.AesGcm.X86

/-- AES-GCM's layout, with the `K` bytes below `SP` apart from the context,
the state and `W`. -/
structure Lay4 (Ctx St W SP : BitVec 32) (K : Nat) : Prop where
  lay : Lay Ctx St W SP 28
  k28 : 28 ≤ K
  sp : K ≤ SP.toNat
  kc : (below SP K).Disjoint ⟨w64 Ctx, 256⟩
  ks : (below SP K).Disjoint ⟨w64 St, 80⟩
  kw : (below SP K).Disjoint ⟨w64 W, 2560⟩

namespace Lay4

variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay4 Ctx St W SP K)
include L

theorem fc : Ctx.toNat + 256 ≤ 2 ^ 32 := L.lay.fc
theorem fs : St.toNat + 80 ≤ 2 ^ 32 := L.lay.fs
theorem fw : W.toNat + 2560 ≤ 2 ^ 32 := L.lay.fw
theorem cs : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 St, 80⟩ := L.lay.cs
theorem cw : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 W, 2560⟩ := L.lay.cw
theorem sb : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 96, 2464⟩ := L.lay.sb

theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := L.lay.st_w ha hd

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := L.lay.ctx_w ha hd

theorem stk_st {a n : Nat} (ha : a + n ≤ 80) :
    (below SP K).Disjoint ⟨w64 St + BitVec.ofNat 64 a, n⟩ := L.ks.sub_right (Lay.stSub ha)

theorem stk_w {a n : Nat} (ha : a + n ≤ 2560) :
    (below SP K).Disjoint ⟨w64 W + BitVec.ofNat 64 a, n⟩ := L.kw.sub_right (Lay.wSub ha)

/-- The stack the calls use, at `esp = SP`. -/
theorem below_sub {k : Nat} (hk : k ≤ K) : Region.Sub (below SP k) (below SP K) :=
  VG.X86.below_sub hk L.sp

/-- What AES-GCM's pieces use below `SP` is within it. -/
theorem below28 : Region.Sub (below SP 28) (below SP K) := L.below_sub L.k28

theorem aW {o : Nat} (ho : o < 2560) : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := L.lay.aW ho
theorem aS {o : Nat} (ho : o < 80) : w64 (St + BitVec.ofNat 32 o) = w64 St + BitVec.ofNat 64 o := L.lay.aS ho
theorem nW {o : Nat} (ho : o < 2560) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o := L.lay.nW ho
theorem nS {o : Nat} (ho : o < 80) : (St + BitVec.ofNat 32 o).toNat = St.toNat + o := L.lay.nS ho
end Lay4

/-- The layout, from its regions' bounds and disjointness. -/
theorem Lay4.of {Ctx St W SP : BitVec 32} {K : Nat} (fc : Ctx.toNat + 256 ≤ 2 ^ 32)
    (fs : St.toNat + 80 ≤ 2 ^ 32) (fw : W.toNat + 2560 ≤ 2 ^ 32) (k28 : 28 ≤ K) (sp : K ≤ SP.toNat)
    (cs : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 St, 80⟩) (cw : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 W, 2560⟩)
    (sa : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W, 16⟩)
    (sb : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 96, 2464⟩)
    (kc : (below SP K).Disjoint ⟨w64 Ctx, 256⟩) (ks : (below SP K).Disjoint ⟨w64 St, 80⟩)
    (kw : (below SP K).Disjoint ⟨w64 W, 2560⟩) : Lay4 Ctx St W SP K :=
  have hb := VG.X86.below_sub (sp := SP) k28 sp
  ⟨⟨fc, fs, fw, by decide, by decide, by omega_using [k28, sp], cs, cw, sa, sb, kc.sub_left hb, ks.sub_left hb,
    kw.sub_left hb⟩, k28, sp, kc, ks, kw⟩

/-- Data apart from the `K` bytes below `SP` is apart from the `k ≤ K`. -/
theorem DataOk.mono {St W SP : BitVec 32} {K k : Nat} {s : State} {D : BitVec 32} {n : Nat}
    (h : DataOk St W SP K s D n) (hk : k ≤ K) (hsp : K ≤ SP.toNat) : DataOk St W SP k s D n :=
  { h with stk := h.stk.sub_left (VG.X86.below_sub hk hsp) }

end VG.Proof.Sm4Gcm.X86

end

end



/-!
# SM4-GCM on x86: calling `vg_sm4_ctr32` from the pieces

Untrusted: everything here is checked by Lean. The arguments of
`vg_sm4_ctr32` in their registers (`CtrReady`): the key schedule at the
context, a counter block `C` and `nb` blocks at `Dp`; the call (`ctrW_ok`,
`CtrOut`) and its constant time (`ctrW_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctr32)

/-- The cipher of the key schedule in the context. -/
abbrev ciphOf (m : Mem) (Ctx : BitVec 32) : Block → Block :=
  Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt m (w64 Ctx))

theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Ctx : BitVec 32}
    (hd : ∀ r ∈ rs, (⟨w64 Ctx, 256⟩ : Region).Disjoint r) :
    ciphOf m' Ctx = ciphOf m Ctx := by
  simp only [ciphOf]
  rw [scheduleAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide)))]

/-- The call of `vg_sm4_ctr32`. -/
abbrev ctrW : Prog isa := ctrCall

/-- Ready for `ctrW`: the arguments of `vg_sm4_ctr32` in their registers. -/
structure CtrReady (Ctx St W SP : BitVec 32) (C Dp : BitVec 32) (nb : Nat) (s : State) : Prop where
  eax : s.gpr .eax = Ctx
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = Dp
  edi : s.gpr .edi = BitVec.ofNat 32 nb
  ebp : s.gpr .ebp = W
  esi : s.gpr .esi = St
  esp : s.gpr .esp = SP
  ctxR : Covers [⟨w64 Ctx, 256⟩] (s.rd ++ s.wr)
  stW : Covers [⟨w64 St, 80⟩] s.wr
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  ctx : s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = Ctx
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : Dp.toNat + 16 * nb ≤ 2 ^ 32
  wC : Covers [⟨w64 C, 16⟩] s.wr
  wD : Covers [⟨w64 Dp, 16 * nb⟩] s.wr
  cd : (⟨w64 C, 16⟩ : Region).Disjoint ⟨w64 Dp, 16 * nb⟩
  kC : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 C, 16⟩
  kD : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 Dp, 16 * nb⟩
  bC : (below SP 1536).Disjoint ⟨w64 C, 16⟩
  bD : (below SP 1536).Disjoint ⟨w64 Dp, 16 * nb⟩
  pC : (keptR W).Disjoint ⟨w64 C, 16⟩
  pD : (keptR W).Disjoint ⟨w64 Dp, 16 * nb⟩

/-- What `ctrW` leaves. -/
structure CtrOut (Ctx St W SP : BitVec 32) (C Dp : BitVec 32) (nb : Nat) (s s' : State) : Prop where
  env : Env Ctx St W SP s'
  frame : Frame [⟨w64 C, 16⟩, ⟨w64 Dp, 16 * nb⟩, below SP 1536] s.mem s'.mem
  out : blocksAt s'.mem (w64 Dp) nb = ctr32 (ciphOf s.mem Ctx) (blockAt s.mem (w64 C)) (blocksAt s.mem (w64 Dp) nb)
  ctr : blockAt s'.mem (w64 C) = Nat.repeat Spec.Gcm.inc32 nb (blockAt s.mem (w64 C))
  ebx : s'.gpr .ebx = s.gpr .ebx
  edi : s'.gpr .edi = s.gpr .edi
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay4 Ctx St W SP K) (hK : K = 1536)
include L hK

theorem CtrReady.call {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : CtrReady Ctx St W SP C Dp nb s) : CtrCall s Ctx C Dp nb := by
  have hsp : below (s.gpr .esp) 1536 = below SP 1536 := by rw [h.esp]
  refine ⟨h.eax, h.edx, h.ebx, h.edi, by rw [h.esp]; have := L.sp; omega_using [hK, this],
    h.kC.sub_left (Region.sub_prefix (by decide)), h.kD.sub_left (Region.sub_prefix (by decide)), h.cd,
    by rw [hsp]; subst hK; exact L.kc.sub_right (Region.sub_prefix (by decide)),
    by rw [hsp]; exact h.bC, by rw [hsp]; exact h.bD, by have := L.fc; omega_using [this], h.fC, h.fD,
    covers_pre h.ctxR (by decide) (by decide), covers_cons h.wC (covers_cons h.wD covers_nil)⟩

theorem CtrReady.kept {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : CtrReady Ctx St W SP C Dp nb s) :
    ∀ r ∈ [(⟨w64 C, 16⟩ : Region), ⟨w64 Dp, 16 * nb⟩, below SP 1536], (keptR W).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.pC
  · exact h.pD
  · subst hK; exact (L.stk_w (by decide)).symm

theorem ctrW_ok {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : CtrReady Ctx St W SP C Dp nb s) :
    WP isa ctrW s (CtrOut Ctx St W SP C Dp nb s) := by
  refine WP.mono (ctr_call (h.call L hK)) fun s₁ g => ?_
  have gf := g.frame
  have hsp : below (s.gpr .esp) 1536 = below SP 1536 := by rw [h.esp]
  rw [hsp] at gf
  have hk := h.kept L hK
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, gf, g.out, g.ctr, g.saved .ebx (by decide), g.saved .edi (by decide),
    g.rd, g.wr⟩
  · rw [g.saved .ebp (by decide), h.ebp]
  · rw [g.saved .esi (by decide), h.esi]
  · rw [g.saved .esp (by decide), h.esp]
  · rw [g.rd, g.wr]; exact h.ctxR
  · rw [g.wr]; exact h.stW
  · rw [g.wr]; exact h.wW
  · rw [ctx_frame gf hk, h.ctx]

theorem ctrW_ct {C Dp : BitVec 32} {nb : Nat} : CT (CtrReady Ctx St W SP C Dp nb) ctrW :=
  ctr_ct (E := SP) fun _ h => ⟨h.call L hK, h.esp⟩

end

end VG.Proof.Sm4Gcm.X86
