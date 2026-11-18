module

public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.AesGcm.X86.Loops
public import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.AesGcm.X86.Frame
import VerifiedGarbage.Proof.AesGcm.X86.Verified
import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.X86
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.Proof.AesGcm.X86.Open
import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Proof.Zeroize.Common
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesGcm.X86.Open
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
meta import VerifiedGarbage.Proof.Zeroize.Common
meta import VerifiedGarbage.Proof.AesGcm.X86.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
meta import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
meta import VerifiedGarbage.Proof.Aes.X86.VariantProof

/-! ### `AesGcm.X86.OpenTo.Dec`, which only this module used -/

section

/-!
# AES-GCM decryption out of place on x86: `open`'s body to a destination

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_to` runs
`open`'s body (`Open.lean`) with `open`'s arguments and the destination
`dst` in the word at `esp` (`dstOf`), which the body keeps as the return
address it never writes. If the tag length is not allowed or the tag is
wrong, `dst` is zeroed (`wipeBad_pc`, `wipeFail_pc`); if the tag is right,
the data are decrypted to `dst` (`decTo_pc`): the whole blocks by
`vg_aes_ctr32_to`, whose last argument `dst` is that word, above the six
registers pushed (`ctrTo_call`, `ctrTo_ct`, from the callee's contract
`Proof.Aes.ctr32ToX86`), and the last bytes copied there and decrypted in
place by `crypt`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32)

/-- The callee's first six arguments, the registers pushed below `E`. -/
abbrev toArgsR (E : BitVec 32) : Region := ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩

abbrev ctrToRd (E K D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 K, 240⟩, toArgsR E, ⟨w64 E, 4⟩, ⟨w64 D, 16 * n⟩]
abbrev ctrToWr (C T S : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 C, 16⟩, ⟨w64 T, 16 * n⟩, ⟨w64 S, 2048⟩]

/-- The six registers `ctrToCall` pushes. -/
abbrev ctrToRegs : List Reg := [.ebp, .edi, .ebx, .edx, .ecx, .eax]

theorem ctrToRegs_esp : Reg.esp ∉ ctrToRegs := by decide

/-- What a call of `vg_aes_ctr32_to` needs: the key schedule at `K` for `R`
rounds, the counter block at `C`, `n` blocks read at `D` and written at `T`
(the word at `esp`), and working space at `S`. -/
structure CtrToCall (s : State) (K C D S T : BitVec 32) (R n : Nat) : Prop where
  eax : s.gpr .eax = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  edi : s.gpr .edi = BitVec.ofNat 32 n
  ebp : s.gpr .ebp = S
  dst : s.mem.readW (w64 (s.gpr .esp)) 32 = T
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 28 ≤ (s.gpr .esp).toNat
  fsp : (s.gpr .esp).toNat + 4 ≤ 2 ^ 32
  kc : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 C, 16⟩
  kt : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 T, 16 * n⟩
  ks : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  ct : (⟨w64 C, 16⟩ : Region).Disjoint ⟨w64 T, 16 * n⟩
  cs : (⟨w64 C, 16⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  ts : (⟨w64 T, 16 * n⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  dc : (⟨w64 D, 16 * n⟩ : Region).Disjoint ⟨w64 C, 16⟩
  dt : (⟨w64 D, 16 * n⟩ : Region).Disjoint ⟨w64 T, 16 * n⟩
  ds : (⟨w64 D, 16 * n⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  bk : (below (s.gpr .esp) 28).Disjoint ⟨w64 K, 240⟩
  bc : (below (s.gpr .esp) 28).Disjoint ⟨w64 C, 16⟩
  bd : (below (s.gpr .esp) 28).Disjoint ⟨w64 D, 16 * n⟩
  bt : (below (s.gpr .esp) 28).Disjoint ⟨w64 T, 16 * n⟩
  bs : (below (s.gpr .esp) 28).Disjoint ⟨w64 S, 2048⟩
  rc : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 C, 16⟩
  rt : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 T, 16 * n⟩
  rs : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  fK : K.toNat + 240 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fT : T.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2048 ≤ 2 ^ 32
  last : Covers [⟨w64 (s.gpr .esp), 4⟩] (s.rd ++ s.wr)
  reads : Covers [⟨w64 K, 240⟩, ⟨w64 D, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨w64 C, 16⟩, ⟨w64 T, 16 * n⟩, ⟨w64 S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32_to` leaves. -/
structure CtrToPost (s : State) (K C D S T : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨w64 C, 16⟩, ⟨w64 T, 16 * n⟩, ⟨w64 S, 2048⟩, below (s.gpr .esp) 28] s.mem s'.mem
  out : blocksAt s'.mem (w64 T) n = ctr32 (aesWith R (bytesAt s.mem (w64 K) (16 * (R + 1))))
    (blockAt s.mem (w64 C)) (blocksAt s.mem (w64 D) n)
  ctr : blockAt s'.mem (w64 C) = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem (w64 C))

namespace CtrToCall
variable {s : State} {K C D S T : BitVec 32} {R n : Nat} (h : CtrToCall s K C D S T R n)
include h

theorem fit : 4 * ctrToRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega_using [this]

theorem n_lt : n < 2 ^ 32 := by have := h.fD; omega_using [this]

theorem args : arg (pushed ctrToRegs s).callEntry 0 = K ∧ arg (pushed ctrToRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed ctrToRegs s).callEntry 2 = C ∧ arg (pushed ctrToRegs s).callEntry 3 = D ∧
    arg (pushed ctrToRegs s).callEntry 4 = BitVec.ofNat 32 n ∧ arg (pushed ctrToRegs s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit ctrToRegs_esp (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.edi, h.ebp]

/-- The last argument: the word at the caller's `esp`, above the frame. -/
theorem arg6 : arg (pushed ctrToRegs s).callEntry 6 = T := by
  obtain hn : 4 * ctrToRegs.length ≤ (s.gpr .esp).toNat := by have := h.fit; omega_using [this]
  obtain e : ((pushed ctrToRegs s).gpr .esp).toNat = (s.gpr .esp).toNat - 24 := by
    rw [pushed_esp, sub_toNat hn]; rfl
  have hsp := h.fsp
  rw [arg_callEntry (by rw [e]; have := h.esp; omega_using [this]) (by rw [e]; omega_using [hsp])]
  obtain ew : ((pushed ctrToRegs s).gpr .esp + BitVec.ofNat 32 (4 * 6)).setWidth 64 = w64 (s.gpr .esp) := by
    rw [pushed_esp]; congr 1; rw [show (4 * ctrToRegs.length : Nat) = 4 * 6 from rfl, BitVec.sub_add_cancel]
  rw [ew, (pushed_frame ctrToRegs_esp hn).readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ret_below (k := 24) (by have := h.esp; omega_using [this])) (by decide)]
  exact h.dst

theorem sub24 : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 28) := below_sub (by omega_using []) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below (s.gpr .esp) 28) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 28) (k := 24) (by omega_using []) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 28 = s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

/-- The callee's first six arguments, below `esp`. -/
theorem argsDisj {X : Region} (hb : (below (s.gpr .esp) 28).Disjoint X) : (toArgsR (s.gpr .esp)).Disjoint X := by
  refine hb.sub_left ?_
  have := below_inner (sp := s.gpr .esp) (a := 24) (b := 28) (k := 0) (by omega_using []) h.esp
  simpa using this

theorem callPre : CallPre Proof.Aes.ctr32ToX86 ctrToRegs (ctrToRd (s.gpr .esp) K D n) (ctrToWr C T S n) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have a6 := h.arg6
  obtain hR := toNat_rounds h.rounds
  obtain hn := toNat_ofNat32 h.n_lt
  obtain eA : argAddr (pushed ctrToRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  obtain eSp : (pushed ctrToRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 28 := by
    rw [callEntry_esp']; rfl
  obtain eL : argAddr (pushed ctrToRegs s).callEntry 6 = w64 (s.gpr .esp) := by
    simp only [argAddr, eSp]
    rw [show s.gpr .esp - BitVec.ofNat 32 28 + BitVec.ofNat 32 (4 + 4 * 6) = s.gpr .esp from
      BitVec.sub_add_cancel _ _]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.ctr32ToX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, a6, eA, eL, eSp, hR, hn]
    refine ⟨trivial, trivial, h.kc, h.kt, h.ks, h.ct, h.cs, h.ts, h.dc, h.dt, h.ds,
      h.argsDisj h.bc, h.argsDisj h.bt, h.argsDisj h.bs, h.rc, h.rt, h.rs,
      h.bc.sub_left h.sub4, h.bt.sub_left h.sub4, h.bs.sub_left h.sub4,
      h.fK, h.fC, h.fD, h.fT, h.fS, ?_, h.rounds⟩
    rw [sub_toNat (by have := h.esp; omega_using [this])]; have := h.fsp; omega_using [this]
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, List.mem_cons_self .., hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    · exact InRegions_append_cons.mpr (.inr (h.last a m ⟨_, List.mem_singleton_self _, hcn⟩))
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a m hi
    obtain ⟨r', hr', hc'⟩ := h.writes a m hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end CtrToCall

theorem ctrTo_call (v : GcmImpl) {s : State} {K C D S T : BitVec 32} {R n : Nat} (h : CtrToCall s K C D S T R n) :
    WP isa (Open.ctrToCall ⟨v.ctr.callee.name, v.ctr.callee.code⟩) s (CtrToPost s K C D S T R n) := by
  obtain hR := toNat_rounds h.rounds
  obtain hn := toNat_ofNat32 h.n_lt
  obtain hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega_using [h']
  unfold Open.ctrToCall
  refine WP.callWith (rs := ctrToRegs) (k := Proof.Aes.ctr32ToX86) v.ctr.okTo v.ctr.nosp (by simp)
    ctrToRegs_esp (by rw [v.ctr.stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega_using [this])
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := h.args
  have a6 := h.arg6
  rw [v.ctr.stack] at f'
  obtain fE := callEntry_frame h.fit ctrToRegs_esp
  rw [show 4 * ctrToRegs.length + 4 = 28 from rfl] at fE
  obtain ⟨hdata, hctr⟩ := post
  simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, a6, hR, hn] at hdata hctr
  -- The pop loses the arguments' frame, below `esp`, apart from the buffers.
  have fL : Frame [below (s.gpr .esp) 28] s₂.mem s'.mem := Frame.below_mono (wr := []) m₂ (by decide) h.esp
  rw [← blocksAt_frame fL (one_disj h.bt) (by have := h.fT; omega_using [hn])] at hdata
  rw [← blockAt_frame fL (one_disj h.bc)] at hctr
  obtain eK := bytesAt_frame fE (p := w64 K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bk.sub_right (Region.sub_prefix hR')).symm) (by omega_using [hR])
  rw [blockAt_frame fE (one_disj h.bc), blocksAt_frame fE (one_disj h.bd) (by have := h.fD; omega_using [hn]),
    eK] at hdata
  rw [blockAt_frame fE (one_disj h.bc)] at hctr
  refine ⟨rd', wr', cs', ?_, hdata, hctr⟩
  exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr

/-- Calls of `vg_aes_ctr32_to` with the same arguments and stack pointer in
both runs are constant time. -/
theorem ctrTo_ct (v : GcmImpl) {I : State → Prop} {K C D S T E : BitVec 32} {R n : Nat}
    (h : ∀ s, I s → CtrToCall s K C D S T R n ∧ s.gpr .esp = E) :
    CT I (Open.ctrToCall ⟨v.ctr.callee.name, v.ctr.callee.code⟩) := by
  refine CT.callWith v.ctr.okTo v.ctr.ctTo (ctrToRd E K D n) (ctrToWr C T S n) fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h₂.args
  have a6 := h₁.arg6
  have b6 := h₂.arg6
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]
  · rw [a6, b6]

end VG.Proof.AesGcm.X86

namespace VG.Proof.AesGcm.X86.OpenTo

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.Open VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxH ctxCiph inc32 gctr)
open VG.Proof.Gcm (Ctr xorKs)

variable {vg : GcmImpl}

/-- The destination: the word at `esp` on entry to the body. -/
abbrev dstOf (s : State) : BitVec 32 := s.mem.readW (w64 (s.gpr .esp)) 32

/-- The `len` bytes at the destination `T`, for the public data `p`, apart
from everything else the body reads or writes. -/
structure DL (p : BitVec 32 × (Nat → BitVec 32)) (T : BitVec 32) : Prop where
  fT : T.toNat + (p.2 7).toNat ≤ 2 ^ 32
  c_t : (⟨w64 (p.2 0), 256⟩ : Region).Disjoint ⟨w64 T, (p.2 7).toNat⟩
  n_t : (⟨w64 (p.2 2), (p.2 3).toNat⟩ : Region).Disjoint ⟨w64 T, (p.2 7).toNat⟩
  a_t : (⟨w64 (p.2 4), (p.2 5).toNat⟩ : Region).Disjoint ⟨w64 T, (p.2 7).toNat⟩
  d_t : (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint ⟨w64 T, (p.2 7).toNat⟩
  g_t : (⟨w64 (p.2 10), (p.2 9).toNat⟩ : Region).Disjoint ⟨w64 T, (p.2 7).toNat⟩
  w_t : (⟨w64 (p.2 8), 2560⟩ : Region).Disjoint ⟨w64 T, (p.2 7).toNat⟩
  r_t : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 T, (p.2 7).toNat⟩
  k_t : (below p.1 32).Disjoint ⟨w64 T, (p.2 7).toNat⟩

/-- The precondition of `open`'s body out of place: `open`'s arguments, the
destination writable and apart, and the word at `esp`, which holds it, readable
(the last argument of `vg_aes_ctr32_to`). -/
structure BodyTo (s : State) : Prop where
  op : OP 11 10 s
  tg : Covers [⟨w64 (arg s 8), (arg s 9).toNat⟩] (s.rd ++ s.wr) ∧
    (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧
    (⟨w64 (arg s 8), (arg s 9).toNat⟩ : Region).Disjoint ⟨w64 (arg s 10), 2560⟩ ∧
    (below (s.gpr .esp) 32).Disjoint ⟨w64 (arg s 8), (arg s 9).toNat⟩
  dl : DL (pubSw 11 8 s) (dstOf s)
  dW : Covers [⟨w64 (dstOf s), (arg s 7).toNat⟩] s.wr
  last : Covers [⟨w64 (s.gpr .esp), 4⟩] (s.rd ++ s.wr)

/-- What a run out of place knows of the destination, from its index. -/
theorem IX.dl {q : OQ} {s₀ : State} (h : IX BodyTo dstOf q s₀) : DL q.1.1 q.1.2 := by
  have := h.pre.dl; rwa [h.pub, h.ext] at this

theorem IX.dW {q : OQ} {s₀ : State} (h : IX BodyTo dstOf q s₀) :
    Covers [⟨w64 q.1.2, (q.1.1.2 7).toNat⟩] s₀.wr := by
  have := h.pre.dW; rwa [h.ext, open_arg h.pub (i := 7) (by decide)] at this

section
variable {p : BitVec 32 × (Nat → BitVec 32)} {T : BitVec 32} (G : OL p) (D : DL p T)
include G D

/-- The destination, with what the pieces write. -/
abbrev tF (p : BitVec 32 × (Nat → BitVec 32)) (T : BitVec 32) : List Region :=
  ⟨w64 T, (p.2 7).toNat⟩ :: oFF p

theorem slot_tF {o n : Nat} (h₁ : 128 ≤ o)
    (h₂ : o + n ≤ auxO ∨ (auxO + 4 ≤ o ∧ o + n ≤ rO) ∨ (rO + 16 ≤ o ∧ o + n ≤ 240)) :
    ∀ r ∈ tF p T, (⟨w64 (p.2 8) + BitVec.ofNat 64 o, n⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [auxO, rO] at h₂; exact D.w_t.sub_left (Lay.wSub (by omega_using [h₂]))
  · exact slot_oF G h₁ h₂ r hr

theorem ctx_tF : ∀ r ∈ tF p T, (⟨w64 (p.2 0), 256⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact D.c_t
  · exact ctx_oF G r hr

theorem aad_tF : ∀ r ∈ tF p T, (⟨w64 (p.2 4), (p.2 5).toNat⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact D.a_t
  · exact aad_oF G r hr

theorem ret_tF : ∀ r ∈ tF p T, (⟨w64 p.1, 4⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact D.r_t
  · exact ret_oF G r hr

/-- `OEnv` after code that writes within the destination and `oFF p` and keeps the registers. -/
theorem OEnv.frameT {s₀ s s' : State} (h : OEnv p s₀ s) (hf : Frame (tF p T) s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : OEnv p s₀ s' :=
  h.frameG G (fun h₁ h₂ => slot_tF G D h₁ h₂) (ctx_tF G D) (aad_tF G D) (ret_tF G D) hf hbp hsi hsp hrd hwr

end

/-! ## Zeroing the destination -/

/-- `cmp ecx, 0`: whether there are bytes to zero. -/
theorem cmp0_ok (u : State) {n : Nat} (hn : n < 2 ^ 32) (h₂ : u.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa (.block [.alu .cmp .ecx (imm 0)]) u fun t => t.mem = u.mem ∧ (∀ r, t.gpr r = u.gpr r) ∧
      t.zf = some (decide (n = 0)) ∧ t.rd = u.rd ∧ t.wr = u.wr := by
  refine WP.of_runBlock ⟨_, by xrun [], ?_⟩
  refine ⟨?_, fun r => ?_, ?_, ?_, ?_⟩
  · simp only [mem_arithFlags]
  · simp only [gpr_arithFlags]
  · simp only [zf_arithFlags, h₂, BitVec.sub_zero, VG.X86.Wp.ofNat_beq_zero hn]
  · simp only [rd_arithFlags]
  · simp only [wr_arithFlags]

/-- One step of the wipe: the byte at `D + j` zeroed. -/
theorem zeroStep_ok (t : State) {D : BitVec 32} {j : Nat} (hd : t.gpr .edx = D + BitVec.ofNat 32 j)
    (ha : t.gpr .eax = 0) (w : InRegions t.wr (w64 (D + BitVec.ofNat 32 j)) 1) :
    ∃ t', runBlock isa [.store8 (at_ .edx 0) .al, .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)] t = some t' ∧
      t'.mem = t.mem.writeW (w64 (D + BitVec.ofNat 32 j)) (0 : BitVec 8) ∧
      t'.gpr .edx = D + BitVec.ofNat 32 (j + 1) ∧ t'.gpr .ecx = t.gpr .ecx - BitVec.ofNat 32 1 ∧
      t'.zf = some (t.gpr .ecx - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by xrun [hd, add_zero32, w], ?_, ?_, ?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_⟩
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [show Reg8.al.reg = Reg.eax from rfl, ha, show BitVec.setWidth 8 (0 : BitVec 32) = 0 by decide]
  · regs [hd, succ_ofNat32]
  · regs []
  · simp only [zf_setMem, zf_setReg, zf_arithFlags, gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq]
  · simp [gpr_setMem, gpr_setReg, gpr_arithFlags, h₁, h₂]
  · simp only [rd_setMem, rd_setReg, rd_arithFlags]
  · simp only [wr_setMem, wr_setReg, wr_arithFlags]

/-- `wipeLoop`: the `n` bytes at `D` zeroed, from `edx = D`, `ecx = n` and
`eax = 0`. -/
theorem wipeLoop_wp (u : State) {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) (hD : D.toNat + n ≤ 2 ^ 32)
    (h₁ : u.gpr .edx = D) (h₂ : u.gpr .ecx = BitVec.ofNat 32 n) (h₀ : u.gpr .eax = 0)
    (hw : Covers [⟨w64 D, n⟩] u.wr) :
    WP isa wipeLoop u fun u' => Proof.Zeroize.Prefix u'.mem (w64 D) n ∧ Frame [⟨w64 D, n⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  unfold wipeLoop
  refine WP.seq (WP.mono (cmp0_ok u hn h₂) fun t ⟨tm, tg, tz, trd, twr⟩ => ?_)
  refine WP.ite (decide (n = 0)) tz (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), by rw [tm]; exact Frame.refl _ _,
      fun r _ _ => tg r, trd, twr⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (body := .block [.store8 (at_ .edx 0) .al, .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)]) (c := .ne)
      (fun (w : Nat) (v : State) => ∃ i, w = n - i ∧ i < n ∧ v.gpr .edx = D + BitVec.ofNat 32 i ∧
        v.gpr .ecx = BitVec.ofNat 32 (n - i) ∧ (∀ r, r ≠ .ecx → r ≠ .edx → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧
        v.wr = u.wr ∧ Frame [⟨w64 D, n⟩] u.mem v.mem ∧ Proof.Zeroize.Prefix v.mem (w64 D) i) ?_ (n - 0) _
      ⟨0, rfl, by omega_using [h0], by rw [tg, h₁, add_zero32], by rw [tg, h₂, Nat.sub_zero], fun r _ _ => tg r, trd, twr,
        by rw [tm]; exact Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    rintro w v ⟨i, rfl, hi, edx, ecx, gv, rdv, wrv, fv, pv⟩
    obtain aD : w64 (D + BitVec.ofNat 32 i) = w64 D + BitVec.ofNat 64 i := w64_add (by omega_using [hD, hi])
    obtain hcn : (⟨w64 D, n⟩ : Region).Contains (w64 D + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi])
    obtain win : InRegions v.wr (w64 (D + BitVec.ofNat 32 i)) 1 := by
      rw [wrv, aD]; exact hw _ _ ⟨_, List.mem_singleton_self _, hcn⟩
    obtain ⟨v', run', mem', edx', ecx', zf', g', rd', wr'⟩ :=
      zeroStep_ok v edx (by rw [gv _ (by decide) (by decide), h₀]) win
    refine WP.of_runBlock ⟨v', run', ?_⟩
    obtain f' : Frame [⟨w64 D, n⟩] u.mem v'.mem := by
      rw [mem', aD]; exact fv.writeW (List.mem_singleton_self _) _ hcn
    obtain p' : Proof.Zeroize.Prefix v'.mem (w64 D) (i + 1) := by
      rw [mem', aD]; exact Proof.Zeroize.prefix_writeW (w := 8) pv (by omega_using [hn, hi])
    obtain g'' : ∀ r, r ≠ .ecx → r ≠ .edx → v'.gpr r = u.gpr r := fun r a b => by rw [g' r a b, gv r a b]
    obtain hz : v'.zf = some (decide (i + 1 = n)) := by rw [zf', ecx, pred_beq hi hn]
    by_cases he : i + 1 = n
    · left
      exact ⟨by simp [eval, hz, he], by rw [← he]; exact p', f', g'', rd'.trans rdv, wr'.trans wrv⟩
    · right
      exact ⟨by simp [eval, hz, he], n - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], edx',
        by rw [ecx', ecx, pred_count hi hn], g'', rd'.trans rdv, wr'.trans wrv, f', p'⟩

/-- The zeros of `Prefix`, as bytes. -/
theorem bytesAt_zeros {m : Mem} {D : Addr} {n : Nat} (h : Proof.Zeroize.Prefix m D n) :
    bytesAt m D n = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact h i (by simpa [bytesAt] using h₁)


section
variable {p : BitVec 32 × (Nat → BitVec 32)} {T : BitVec 32} (G : OL p) (D : DL p T)
include G D

omit D in
/-- `wipeArgs`: the destination in `edx`, `len` in `ecx` and zero in `eax`. -/
theorem wipeArgs_ok {s₀ s : State} (h : OEnv p s₀ s) (hT : s.mem.readW (w64 p.1) 32 = T)
    (hr : InRegions (s.rd ++ s.wr) (w64 p.1) 4) : ∃ s₁, runBlock isa wipeArgs s = some s₁ ∧
      s₁.gpr .edx = T ∧ s₁.gpr .ecx = BitVec.ofNat 32 (p.2 7).toNat ∧ s₁.gpr .eax = 0 ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  have L := G.L
  obtain lR := h.env.wIn' (d := lenO) (n := 4) (by decide)
  have lv := h.lenO
  rw [slotv_eq] at lv
  obtain hr' : InRegions (s.rd ++ s.wr) (w64 (s.gpr .esp + BitVec.ofNat 32 0)) 4 := by
    rw [add_zero32, h.env.esp]; exact hr
  refine ⟨_, by xrun [wipeArgs, h.env.ebp, L.aW, lR, hr'], ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_⟩
  · regs [add_zero32]; rw [h.env.esp]; exact hT
  · regs []; simp only [lenO] at lv; rw [lv, ofNat_toNat32]
  · regs []; rfl
  · simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_setReg_of_ne _ _ h₃]
  all_goals mems []

/-- `wipe`: the `len` bytes at the destination zeroed, and `eax := 0`. -/
theorem wipe_ok {s₀ s : State} (h : OEnv p s₀ s) (hT : s.mem.readW (w64 p.1) 32 = T)
    (hr : InRegions (s.rd ++ s.wr) (w64 p.1) 4) (hw : Covers [⟨w64 T, (p.2 7).toNat⟩] s.wr) :
    WP isa wipe s fun s' => OEnv p s₀ s' ∧ s'.gpr .eax = 0 ∧
      bytesAt s'.mem (w64 T) (p.2 7).toNat = List.replicate (p.2 7).toNat 0 ∧
      Frame [⟨w64 T, (p.2 7).toNat⟩] s.mem s'.mem := by
  obtain ⟨s₁, run, dx, cx, ax, g₁, m₁, rd₁, wr₁⟩ := wipeArgs_ok G h hT hr
  unfold wipe
  refine WP.seq (WP.of_runBlock ⟨s₁, run, ?_⟩)
  refine WP.mono (wipeLoop_wp s₁ (p.2 7).isLt D.fT dx cx ax (by rw [wr₁]; exact hw))
    fun s' ⟨pz, fz, gz, rdz, wrz⟩ => ?_
  rw [m₁] at fz
  obtain gs : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r := fun r a b c => by
    rw [gz r b c, g₁ r a b c]
  refine ⟨OEnv.frameT G D h (fz.mono fun r hr => by simp at hr; simp [hr]) (gs _ (by decide) (by decide) (by decide))
      (gs _ (by decide) (by decide) (by decide)) (gs _ (by decide) (by decide) (by decide)) (rdz.trans rd₁)
      (wrz.trans wr₁), by rw [gz _ (by decide) (by decide), ax], bytesAt_zeros pz, fz⟩

end

/-- `wipe` is constant time when the destination, `len`, `esp` and `W` are
the same in both runs. -/
theorem wipe_ct {I : State → Prop} {E W T : BitVec 32} {n : Nat}
    (hI : ∀ s, I s → s.gpr .esp = E ∧ s.gpr .ebp = W ∧ ∃ s₁, runBlock isa wipeArgs s = some s₁ ∧
      s₁.gpr .edx = T ∧ s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.gpr .eax = 0) : CT I wipe := by
  unfold wipe
  refine CT.seq (J := fun s => s.gpr .edx = T ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧ s.gpr .eax = 0)
    (CT.taint [.esp, .ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [(hI _ h₁).1, (hI _ h₂).1]
      · rw [(hI _ h₁).2.1, (hI _ h₂).2.1]) (by taint_decide))
    (fun s h => by
      obtain ⟨-, -, s₁, run, d, c, a⟩ := hI s h
      exact WP.of_runBlock ⟨s₁, run, d, c, a⟩)
    (CT.taint [.edx, .ecx, .eax] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]) (by taint_decide))

/-- The word at `esp`, the destination, may be read. -/
theorem IX.retIn {q : OQ} {s₀ s : State} (hx : IX BodyTo dstOf q s₀) (h : OEnv q.1.1 s₀ s) :
    InRegions (s.rd ++ s.wr) (w64 q.1.1.1) 4 := by
  rw [h.rd, h.wr, ← pubSw_esp hx.pub]
  exact hx.pre.last _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- The destination, at `esp`. -/
theorem IX.retT {q : OQ} {s₀ s : State} (hx : IX BodyTo dstOf q s₀) (h : OEnv q.1.1 s₀ s) :
    s.mem.readW (w64 q.1.1.1) 32 = q.1.2 := by
  rw [h.ret, ← pubSw_esp hx.pub]; exact hx.ext

/-- What a run out of place knows, from the state its body entered in and
its index, to zero the destination. -/
theorem wipeFacts {q : OQ} {s₀ s : State} (hx : IX BodyTo dstOf q s₀) (h : OEnv q.1.1 s₀ s) :
    OL q.1.1 ∧ DL q.1.1 q.1.2 ∧ s.mem.readW (w64 q.1.1.1) 32 = q.1.2 ∧
      InRegions (s.rd ++ s.wr) (w64 q.1.1.1) 4 ∧ Covers [⟨w64 q.1.2, (q.1.1.2 7).toNat⟩] s.wr := by
  exact ⟨hx.pre.op.ol rfl (by decide) hx.pub, IX.dl hx, IX.retT hx h, IX.retIn hx h, by rw [h.wr]; exact IX.dW hx⟩

/-- `wipe` when the tag length is not allowed. -/
theorem wipeBad_pc (q : OQ) :
    Pc (fun s₀ s => OEnt q.1.1 s₀ s ∧ slotv s.mem (q.1.1.2 8) tglO = BitVec.ofNat 32 (q.1.1.2 9).toNat ∧
        IX BodyTo dstOf q s₀ ∧ s.zf = some true) wipe
      (fun s₀ s => OEnv q.1.1 s₀ s ∧ IX BodyTo dstOf q s₀ ∧ s.gpr .eax = 0 ∧
        bytesAt s.mem (w64 q.1.2) (q.1.1.2 7).toNat = List.replicate (q.1.1.2 7).toNat 0) := by
  refine ⟨fun s₀ s ⟨h, _, hx, _⟩ => ?_, wipe_ct (E := q.1.1.1) (W := q.1.1.2 8) (T := q.1.2)
    (n := (q.1.1.2 7).toNat) fun s ⟨s₀, h, _, hx, _⟩ => ?_⟩
  · obtain ⟨G, D, hT, hr, hw⟩ := wipeFacts hx h.o
    exact WP.mono (wipe_ok G D h.o hT hr hw) fun s' ⟨o, ax, hz, _⟩ => ⟨o, hx, ax, hz⟩
  · obtain ⟨G, D, hT, hr, -⟩ := wipeFacts hx h.o
    obtain ⟨s₁, run, d, c, a, -⟩ := wipeArgs_ok G h.o hT hr
    exact ⟨h.o.env.esp, h.o.env.ebp, s₁, run, d, c, a⟩

/-- `wipe` when the tag is wrong. -/
theorem wipeFail_pc (q : OQ) (hf : q.2 = false) :
    Pc (OC BodyTo dstOf q) wipe
      (OD BodyTo dstOf (fun p x s => bytesAt s.mem (w64 x) (p.2 7).toNat)
        (fun p _ => List.replicate (p.2 7).toNat 0) q) := by
  refine ⟨fun s₀ s h => ?_, wipe_ct (E := q.1.1.1) (W := q.1.1.2 8) (T := q.1.2)
    (n := (q.1.1.2 7).toNat) fun s ⟨s₀, h⟩ => ?_⟩
  · obtain ⟨G, D, hT, hr, hw⟩ := wipeFacts h.ix h.o
    refine WP.mono (wipe_ok G D h.o hT hr hw) fun s' ⟨o, ax, hz, fz⟩ => ⟨o, h.ix, ?_, ?_⟩
    · rw [slotv_eq, slot_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact D.w_t.sub_left (Lay.wSub (by decide)), ← slotv_eq]
      exact h.aux
    · rw [hf]; exact hz
  · obtain ⟨G, D, hT, hr, -⟩ := wipeFacts h.ix h.o
    obtain ⟨s₁, run, d, c, a, -⟩ := wipeArgs_ok G h.o hT hr
    exact ⟨h.o.env.esp, h.o.env.ebp, s₁, run, d, c, a⟩

/-! ## Decrypting to the destination -/

open VG.Proof.Gcm in
/-- `Proof.Gcm.ctr_whole` out of place: `nb` blocks read at `sp` and written
at `dp`. -/
theorem ctr_whole_to {m m' : Mem} {cb ks sp dp : Addr} {ciph : Block → Block} {icb : Block} {n nb : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 = 0)
    (hd : blocksAt m' dp nb = Spec.Gcm.ctr32 ciph (blockAt m cb) (blocksAt m sp nb))
    (hc : blockAt m' cb = Nat.repeat inc32 nb (blockAt m cb)) :
    bytesAt m' dp (16 * nb) = xorKs ciph icb n (bytesAt m sp (16 * nb)) ∧ Ctr m' cb ks ciph icb (n + 16 * nb) := by
  obtain hcb : blockAt m cb = Nat.repeat inc32 (n / 16) icb := by rw [h.1]; congr 1; omega_using [h0]
  refine ⟨?_, ?_, fun h1 => absurd (by omega_using [h0]) h1⟩
  · refine list_ext (by simp [length_xorKs, length_bytesAt]) fun k hk => ?_
    simp only [length_bytesAt] at hk
    rw [getD_xorKs _ _ _ _ (by rw [length_bytesAt]; exact hk), getD_bytesAt' _ _ hk,
      getD_bytesAt' _ _ hk]
    obtain hq : k / 16 < nb := by omega_using [hk]
    obtain e₁ := congrArg (fun L => L.getD (k / 16) 0) hd
    rw [ctr32_getD _ _ _ (by rw [length_blocksAt]; exact hq), blocksAt_getD _ _ _ hq,
      blocksAt_getD _ _ _ hq] at e₁
    obtain ea : ∀ a : Addr, a + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (16 * (k / 16)) + BitVec.ofNat 64 (k % 16) :=
      fun a => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_using []
    rw [ea dp, ea sp, bytes_toBytes_blockAt m' _ (by omega_using []), bytes_toBytes_blockAt m _ (by omega_using []), e₁,
      Proof.Aes.toBytes_xor _ _ (by omega_using []), ksByte, hcb, ← repeat_add,
      show (n + k) / 16 = k / 16 + n / 16 by omega_using [h0], show (n + k) % 16 = k % 16 by omega_using [h0]]
  · rw [hc, hcb, ← repeat_add]; congr 1; omega_using [h0]

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

/-- The first block of `wholeTo`: the data in `ebx`, the number of whole
blocks in `edi`, and ZF set if there are none. -/
theorem wsplit_ok {s₀ s : State} (h : OEnv p s₀ s) :
    ∃ s', runBlock isa [.mov .ebx (slot dataO), .mov .edi (slot lenO), .shift .shr .edi 4,
        .alu .test .edi (.reg .edi)] s = some s' ∧ s'.gpr .ebx = p.2 6 ∧
      s'.gpr .edi = BitVec.ofNat 32 ((p.2 7).toNat / 16) ∧ s'.zf = some (decide ((p.2 7).toNat / 16 = 0)) ∧
      (∀ r, r ≠ .ebx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have L := G.L
  have hd := h.dataO
  have hn := h.lenO
  rw [← ofNat_toNat32 (p.2 7)] at hn
  obtain hr := (p.2 7).isLt
  obtain hsh := shr4 hr
  refine ⟨_, by xrun [h.env.ebp, L.aW, h.env.wIn', hd, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hsh]
  · simp only [zf_setMem, gpr_setMem, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
      reduceCtorEq, hsh]
    rw [and_self_beq32 (by omega_using [])]
  · intro q h₁ h₂; simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, ite_false]
  all_goals rfl

end

/-- The cipher and the first counter block of the data, for the public data
`p`. -/
abbrev ciphP (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : Block → Block :=
  ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat

abbrev icbP (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : Block := inc32 (jOf p s₀)

/-- After the first block of `wholeTo`. -/
structure W1 (p : BitVec 32 × (Nat → BitVec 32)) (T : BitVec 32) (s₀ s : State) : Prop where
  o : OEnv p s₀ s
  ix : IX BodyTo dstOf ((p, T), true) s₀
  aux : slotv s.mem (p.2 8) auxO = BitVec.ofNat 32 1
  data : bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat
  cb : blockAt s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 48) = icbP p s₀
  ebx : s.gpr .ebx = p.2 6
  edi : s.gpr .edi = BitVec.ofNat 32 ((p.2 7).toNat / 16)
  zf : s.zf = some (decide ((p.2 7).toNat / 16 = 0))

/-- After `wholeTo`: the whole blocks decrypted to the destination. -/
structure DW (p : BitVec 32 × (Nat → BitVec 32)) (T : BitVec 32) (s₀ s : State) : Prop where
  o : OEnv p s₀ s
  ix : IX BodyTo dstOf ((p, T), true) s₀
  aux : slotv s.mem (p.2 8) auxO = BitVec.ofNat 32 1
  data : bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat
  whole : bytesAt s.mem (w64 T) (16 * ((p.2 7).toNat / 16)) =
    xorKs (ciphP p s₀) (icbP p s₀) 0 (bytesAt s₀.mem (w64 (p.2 6)) (16 * ((p.2 7).toNat / 16)))
  ctr : CtrS s.mem (stOf (p.2 8)) (ciphP p s₀) (icbP p s₀) (16 * ((p.2 7).toNat / 16))

theorem IX.fsp {q : OQ} {s₀ : State} (h : IX BodyTo dstOf q s₀) : q.1.1.1.toNat + 4 ≤ 2 ^ 32 := by
  have := h.pre.op.fg; rw [pubSw_esp h.pub] at this; omega_using [this]


theorem region_sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

section
variable {p : BitVec 32 × (Nat → BitVec 32)} {T : BitVec 32} (G : OL p) (D : DL p T)
include G D

omit D in
/-- The counter block, in `W`. -/
theorem cb_w : Region.Sub ⟨w64 (stOf (p.2 8) + BitVec.ofNat 32 48), 16⟩ ⟨w64 (p.2 8), 2560⟩ := by
  rw [G.L.aS (by decide), st_eq G]; exact Lay.wSub (by decide)

/-- The call of `vg_aes_ctr32_to` on the whole blocks, with its arguments
set up (`ctrArgs`). -/
theorem toCall {s₀ s : State} (h : W1 p T s₀ s) {s₁ : State}
    (ax : s₁.gpr .eax = p.2 0) (cx : s₁.gpr .ecx = BitVec.ofNat 32 (p.2 1).toNat)
    (dx : s₁.gpr .edx = stOf (p.2 8) + BitVec.ofNat 32 48) (bp : s₁.gpr .ebp = p.2 8 + BitVec.ofNat 32 512)
    (g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → s₁.gpr r = s.gpr r) (m : s₁.mem = s.mem)
    (rd : s₁.rd = s.rd) (wr : s₁.wr = s.wr) :
    CtrToCall s₁ (p.2 0) (stOf (p.2 8) + BitVec.ofNat 32 48) (p.2 6) (p.2 8 + BitVec.ofNat 32 512) T
      (p.2 1).toNat ((p.2 7).toNat / 16) := by
  have L := G.L
  obtain hk : 16 * ((p.2 7).toNat / 16) ≤ (p.2 7).toNat := Nat.mul_div_le _ _
  obtain esp : s₁.gpr .esp = p.1 := by rw [g _ (by decide) (by decide) (by decide) (by decide), h.o.env.esp]
  obtain eS := L.aW (o := 512) (by decide)
  obtain cw := cb_w G
  have hsp := L.sp
  obtain k28 : Region.Sub (below p.1 28) (below p.1 32) := VG.X86.below_sub (by decide) hsp
  have hn := G.fd
  refine ⟨ax, cx, dx, by rw [g _ (by decide) (by decide) (by decide) (by decide), h.ebx],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.edi], bp, ?_, G.rounds, by rw [esp]; omega_using [hsp],
    by rw [esp]; exact IX.fsp h.ix, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by have := L.fc; omega_using [this], ?_, by have := G.fd; omega_using [hn], by have := D.fT; omega_using [this], ?_, ?_, ?_, ?_⟩
  · rw [m, esp, h.o.ret, ← pubSw_esp h.ix.pub]; exact h.ix.ext
  · exact (L.cw.sub_left (Region.sub_prefix (by decide))).sub_right cw
  · exact (D.c_t.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix hk)
  · rw [eS]; exact (L.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact (D.w_t.sub_left cw).sub_right (Region.sub_prefix hk)
  · rw [eS, L.aS (by decide)]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · rw [eS]; exact ((D.w_t.sub_left (Lay.wSub (by decide))).sub_right (Region.sub_prefix hk)).symm
  · exact (G.d_w.sub_left (Region.sub_prefix hk)).sub_right cw
  · exact (D.d_t.sub_left (Region.sub_prefix hk)).sub_right (Region.sub_prefix hk)
  · rw [eS]; exact (G.d_w.sub_left (Region.sub_prefix hk)).sub_right (Lay.wSub (by decide))
  · rw [esp]; exact (L.kc.sub_right (Region.sub_prefix (by decide))).sub_left k28
  · rw [esp]; exact (L.kw.sub_right cw).sub_left k28
  · rw [esp]; exact (G.k_d.sub_right (Region.sub_prefix hk)).sub_left k28
  · rw [esp]; exact (D.k_t.sub_right (Region.sub_prefix hk)).sub_left k28
  · rw [esp, eS]; exact (L.kw.sub_right (Lay.wSub (by decide))).sub_left k28
  · rw [esp]; exact G.r_w.sub_right cw
  · rw [esp]; exact D.r_t.sub_right (Region.sub_prefix hk)
  · rw [esp, eS]; exact G.r_w.sub_right (Lay.wSub (by decide))
  · rw [L.nS (by decide)]; have := L.fs; omega_using [this]
  · rw [L.nW (by decide)]; have := L.fw; omega_using [this]
  · rw [rd, wr, esp, h.o.rd, h.o.wr, ← pubSw_esp h.ix.pub]; exact h.ix.pre.last
  · rw [rd, wr]
    exact covers_cons (covers_pre h.o.env.ctxR (by decide) (by decide))
      (covers_cons (covers_pre h.o.dIn hk (by omega_using [])) covers_nil)
  · rw [wr]
    refine covers_cons ?_ (covers_cons (covers_pre (by rw [h.o.wr]; exact IX.dW h.ix) hk (by omega_using []))
      (covers_cons (by rw [eS]; exact h.o.env.wC (by decide)) covers_nil))
    rw [L.aS (by decide)]; exact h.o.env.stC (by decide)

omit D in
/-- What the call of `vg_aes_ctr32_to` writes, within what the pieces out of
place may write. -/
theorem callFr_tF {m m' : Mem}
    (hf : Frame [⟨w64 (stOf (p.2 8) + BitVec.ofNat 32 48), 16⟩, ⟨w64 T, 16 * ((p.2 7).toNat / 16)⟩,
      ⟨w64 (p.2 8 + BitVec.ofNat 32 512), 2048⟩, below p.1 28] m m') : Frame (tF p T) m m' := by
  have L := G.L
  refine hf.sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩, by simp, ?_⟩
    rw [L.aS (by decide), st_eq G]; exact Offset.sub _ (by decide) (by decide)
  · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (Nat.mul_div_le _ _)⟩
  · refine ⟨wsR (p.2 8), by simp, ?_⟩
    rw [L.aW (by decide)]; exact Offset.sub _ (by decide) (by decide)
  · exact ⟨below p.1 32, by simp, VG.X86.below_sub (by decide) G.L.sp⟩

omit D in
/-- A region apart from `W`, the whole blocks of the destination and the
stack, apart from what the call of `vg_aes_ctr32_to` writes. -/
theorem callFr_disj {X : Region} (hw : X.Disjoint ⟨w64 (p.2 8), 2560⟩)
    (ht : X.Disjoint ⟨w64 T, 16 * ((p.2 7).toNat / 16)⟩) (hk : (below p.1 32).Disjoint X) :
    ∀ r ∈ [(⟨w64 (stOf (p.2 8) + BitVec.ofNat 32 48), 16⟩ : Region), ⟨w64 T, 16 * ((p.2 7).toNat / 16)⟩,
      ⟨w64 (p.2 8 + BitVec.ofNat 32 512), 2048⟩, below p.1 28], X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (cb_w G)
  · exact ht
  · rw [G.L.aW (by decide)]; exact hw.sub_right (Lay.wSub (by decide))
  · exact (hk.sub_left (VG.X86.below_sub (by decide) G.L.sp)).symm

theorem wholeCall_wp (vg : GcmImpl) {s₀ s : State} (h : W1 p T s₀ s) :
    WP isa (.seq (.block ctrArgs) (.seq (Open.ctrToCall ⟨vg.ctr.callee.name, vg.ctr.callee.code⟩)
      (.block unscr))) s (DW p T s₀) := by
  have L := G.L
  obtain hk : 16 * ((p.2 7).toNat / 16) ≤ (p.2 7).toNat := Nat.mul_div_le _ _
  obtain ⟨s₁, run, ax, cx, dx, bp, g, m, rd, wr⟩ := ctrArgs_ok L h.o.env h.o.rounds
  obtain hc := toCall G D h ax cx dx bp g m rd wr
  obtain esp₁ : s₁.gpr .esp = p.1 := by rw [g _ (by decide) (by decide) (by decide) (by decide), h.o.env.esp]
  refine WP.seq (WP.of_runBlock ⟨s₁, run, ?_⟩)
  refine WP.seq (WP.mono (ctrTo_call vg hc) fun s₂ g₂ => ?_)
  obtain bp₂ : s₂.gpr .ebp = p.2 8 + BitVec.ofNat 32 512 := by rw [g₂.saved .ebp (by decide), bp]
  refine WP.of_runBlock ⟨_, by xrun [unscr, bp₂], ?_⟩
  have f₂ := g₂.frame
  rw [esp₁, m] at f₂
  obtain hF : Frame (tF p T) s.mem s₂.mem := callFr_tF G f₂
  have out := g₂.out
  have ctr := g₂.ctr
  obtain hci : Spec.Gcm.aesWith (p.2 1).toNat (bytesAt s₁.mem (w64 (p.2 0)) (16 * ((p.2 1).toNat + 1))) = ciphP p s₀ := by
    rw [m]; exact h.o.ciph
  rw [hci, L.aS (by decide), m] at out
  rw [L.aS (by decide), m] at ctr
  obtain h0 : Ctr s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 48) (w64 (stOf (p.2 8)) + BitVec.ofNat 64 64)
      (ciphP p s₀) (icbP p s₀) 0 := Proof.Gcm.ctr_zero _ _ _ _ h.cb
  obtain ⟨wh, ct⟩ := ctr_whole_to h0 (by decide) out ctr
  obtain hsrc := congrArg (List.take (16 * ((p.2 7).toNat / 16))) h.data
  rw [bytesAt_take _ _ hk, bytesAt_take _ _ hk] at hsrc
  rw [hsrc] at wh
  rw [Nat.zero_add] at ct
  obtain esi : s₂.gpr .esi = s.gpr .esi := by
    rw [g₂.saved .esi (by decide), g _ (by decide) (by decide) (by decide) (by decide)]
  obtain esp : s₂.gpr .esp = s.gpr .esp := by
    rw [g₂.saved .esp (by decide), g _ (by decide) (by decide) (by decide) (by decide)]
  refine ⟨OEnv.frameT G D h.o (by mems []; exact hF) (by regs [bp₂]; rw [h.o.env.ebp]; exact BitVec.add_sub_cancel _ _)
      (by regs [esi]) (by regs [esp]) (by mems [g₂.rd, rd]) (by mems [g₂.wr, wr]), h.ix, ?_, ?_, ?_, ?_⟩
  · mems [slotv_eq]
    rw [slot_frame f₂ fun r hr => ?_, ← slotv_eq]
    · exact h.aux
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [L.aS (by decide), st_eq G]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact (D.w_t.sub_left (Lay.wSub (by decide))).sub_right (Region.sub_prefix hk)
    · rw [L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · refine (Region.Disjoint.sub_left (L.stk_w ?_) (VG.X86.below_sub (by decide) L.sp)).symm; decide
  · mems []
    rw [bytesAt_frame f₂ (callFr_disj G G.d_w (D.d_t.sub_right (Region.sub_prefix hk)) G.k_d)
      (by have := G.fd; omega_using [])]
    exact h.data
  · mems []; exact wh
  · mems []; exact ct

theorem wholeCall_ct (vg : GcmImpl) :
    CT (fun s => ∃ s₀, W1 p T s₀ s) (.seq (.block ctrArgs)
      (.seq (Open.ctrToCall ⟨vg.ctr.callee.name, vg.ctr.callee.code⟩) (.block unscr))) := by
  have L := G.L
  refine CT.seq (J := fun s => CtrToCall s (p.2 0) (stOf (p.2 8) + BitVec.ofNat 32 48) (p.2 6)
      (p.2 8 + BitVec.ofNat 32 512) T (p.2 1).toNat ((p.2 7).toNat / 16) ∧ s.gpr .esp = p.1)
    (CT.taint [.ebp, .esi] (fun s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.o.env.ebp, h₂.o.env.ebp]
      · rw [h₁.o.env.esi, h₂.o.env.esi]) (by taint_decide)) (fun s ⟨s₀, h⟩ => ?_) ?_
  · obtain ⟨s₁, run, ax, cx, dx, bp, g, m, rd, wr⟩ := ctrArgs_ok L h.o.env h.o.rounds
    exact WP.of_runBlock ⟨s₁, run, toCall G D h ax cx dx bp g m rd wr,
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.o.env.esp]⟩
  refine CT.seq (J := fun s => s.gpr .ebp = p.2 8 + BitVec.ofNat 32 512) (ctrTo_ct vg (E := p.1) fun s h => h)
    (fun s h => WP.mono (ctrTo_call vg h.1) fun s' g => by rw [g.saved .ebp (by decide), h.1.ebp]) ?_
  exact CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

/-- `wholeTo`: the whole blocks decrypted to the destination. -/
theorem wholeTo_pc (vg : GcmImpl) :
    Pc (OC BodyTo dstOf ((p, T), true)) (wholeTo ⟨vg.ctr.callee.name, vg.ctr.callee.code⟩) (DW p T) := by
  have L := G.L
  unfold wholeTo
  refine Pc.seq (Q := W1 p T) (Pc.taint [.ebp] (fun s₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s', run, bx, di, zf, g, m, rd, wr⟩ := wsplit_ok G h.o
    refine WP.of_runBlock ⟨s', run, h.o.frame G (by rw [m]; exact Frame.refl _ _)
      (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) rd wr, h.ix,
      by rw [m]; exact h.aux, by rw [m]; exact h.data, by rw [m]; exact h.cb, bx, di, zf⟩
  refine Pc.ite (decide ((p.2 7).toNat / 16 = 0)) (fun _ _ h => h.zf) (fun hb => ?_) (fun hb => ?_)
  · have h0 : (p.2 7).toNat / 16 = 0 := by simpa using hb
    refine Pc.mono Pc.nil (fun _ _ h => h) fun s₀ s h => ⟨h.o, h.ix, h.aux, h.data, ?_, ?_⟩
    · rw [h0]; rfl
    · rw [h0]; exact Proof.Gcm.ctr_zero _ _ _ _ h.cb
  · exact ⟨fun s₀ s h => wholeCall_wp G D vg h, wholeCall_ct G D vg⟩

end

/-- The result out of place: the `len` bytes at the destination, zeros if the
tag is wrong. -/
abbrev outTo (p : BitVec 32 × (Nat → BitVec 32)) (x : BitVec 32) (s : State) : List Byte :=
  bytesAt s.mem (w64 x) (p.2 7).toNat

abbrev fbTo (p : BitVec 32 × (Nat → BitVec 32)) (_ : State) : List Byte := List.replicate (p.2 7).toNat 0

/-- After the keystream block for the last bytes: the bytes XORed with it are
those of the keystream from byte `16 k` on. -/
structure KS (p : BitVec 32 × (Nat → BitVec 32)) (T : BitVec 32) (s₀ s : State) : Prop where
  o : OEnv p s₀ s
  ix : IX BodyTo dstOf ((p, T), true) s₀
  aux : slotv s.mem (p.2 8) auxO = BitVec.ofNat 32 1
  data : bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat
  whole : bytesAt s.mem (w64 T) (16 * ((p.2 7).toNat / 16)) =
    xorKs (ciphP p s₀) (icbP p s₀) 0 (bytesAt s₀.mem (w64 (p.2 6)) (16 * ((p.2 7).toNat / 16)))
  kb : ∀ d : List Byte, d.length = (p.2 7).toNat % 16 →
    List.zipWith (· ^^^ ·) d (bytesAt s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 64) ((p.2 7).toNat % 16)) =
      xorKs (ciphP p s₀) (icbP p s₀) (16 * ((p.2 7).toNat / 16)) d

section
variable {p : BitVec 32 × (Nat → BitVec 32)} {T : BitVec 32} (G : OL p) (D : DL p T)
include G D

omit D in
/-- `tailLen`: `ecx` the number of the last bytes, ZF set if there are none. -/
theorem tailLen_ok {s₀ s : State} (h : OEnv p s₀ s) :
    ∃ s', runBlock isa tailLen s = some s' ∧ s'.gpr .ecx = BitVec.ofNat 32 ((p.2 7).toNat % 16) ∧
      s'.zf = some (decide ((p.2 7).toNat % 16 = 0)) ∧ (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have L := G.L
  have hn := h.lenO
  rw [← ofNat_toNat32 (p.2 7)] at hn
  obtain hlt := (p.2 7).isLt
  obtain hand := and15 (BitVec.ofNat 32 (p.2 7).toNat)
  rw [toNat_ofNat32 hlt] at hand
  refine ⟨_, by xrun [tailLen, h.env.ebp, L.aW, h.env.wIn', hn], ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · regs [hand]
  · simp only [zf_setMem, gpr_setMem, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
      reduceCtorEq, hand]
    rw [and_self_beq32 (by omega_using [])]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, ite_false]
  all_goals rfl

/-- The keystream block for the last bytes, after the whole blocks. -/
theorem ks_pc (vg : GcmImpl) (h0 : (p.2 7).toNat % 16 ≠ 0) :
    Pc (DW p T) (.seq (.block ksArgs) (.seq (ctrCall vg.callees) (.block unscr))) (KS p T) := by
  have L := G.L
  obtain hk : 16 * ((p.2 7).toNat / 16) ≤ (p.2 7).toNat := Nat.mul_div_le _ _
  refine Pc.seq (Q := fun s₀ s => ∃ u, DW p T s₀ u ∧ s.mem = Cmac.zero4 u.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 64) ∧
      CtrReady (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 (p.2 1).toNat (stOf (p.2 8) + BitVec.ofNat 32 48)
        (stOf (p.2 8) + BitVec.ofNat 32 64) 1 s ∧ s.rd = u.rd ∧ s.wr = u.wr)
    (Pc.taint [.ebp, .esi] (fun s₀ s h => WP.mono (ksReady L rfl h.o.env h.o.rounds)
        fun s' ⟨m, c, rd, wr⟩ => ⟨s, h, m, c, rd, wr⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.o.env.ebp, h₂.o.env.ebp]
        · rw [h₁.o.env.esi, h₂.o.env.esi]) (by taint_decide)) ?_
  refine Pc.mono (Pc.of (I := CtrReady (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 (p.2 1).toNat
      (stOf (p.2 8) + BitVec.ofNat 32 48) (stOf (p.2 8) + BitVec.ofNat 32 64) 1)
      (fun _ h => ctrW_ok L rfl h) (ctrW_ct L rfl) _ fun _ _ ⟨_, _, _, g, _⟩ => g) (fun _ _ h => h)
    fun s₀ s₂ ⟨s₁, ⟨u, h, m₁, _, rd₁, wr₁⟩, g⟩ => ?_
  obtain ⟨hks, hcb⟩ := ksBlock_of L m₁ g
  obtain eC := L.aS (o := 48) (by decide)
  obtain eK := L.aS (o := 64) (by decide)
  have gf := g.frame
  rw [eC, eK] at gf
  obtain fz : Frame [⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 64, 16⟩] u.mem s₁.mem := by
    rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  -- What the two write, within `oF`.
  obtain sW : ∀ {d k : Nat}, d + k ≤ 80 → Region.Sub ⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 d, k⟩
      ⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩ := fun hdk => by
    rw [st_eq G]; exact Offset.sub _ (by omega_using []) (by omega_using [hdk])
  obtain f : Frame (tF p T) u.mem s₂.mem := by
    refine Frame.trans (fz.sub fun r hr => ?_) (gf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sW (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, sW (by decide)⟩
      · exact ⟨_, by simp, sW (by decide)⟩
      · exact ⟨wsR (p.2 8), by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨below p.1 32, by simp, fun _ h => h⟩
  -- Through both writes, for a region apart from them.
  obtain two : ∀ {X : Region} {n : Nat}, n ≤ 2 ^ 64 → (∀ r ∈ [(⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 48, 16⟩ : Region),
      ⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 64, 16 * 1⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 512, 2048⟩, below p.1 32],
      X.Disjoint r) → X = ⟨X.base, n⟩ → bytesAt s₂.mem X.base n = bytesAt u.mem X.base n := by
    intro X n hn hX e
    obtain hz : ∀ r ∈ [(⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 64, 16⟩ : Region)], (⟨X.base, n⟩ : Region).Disjoint r :=
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← e]; exact hX _ (by simp)
    rw [bytesAt_frame gf (fun r hr => by rw [← e]; exact hX r hr) hn, bytesAt_frame fz hz hn]
  obtain ciph₁ : ciphOf s₁.mem (p.2 0) (p.2 1).toNat = ciphP p s₀ := by
    rw [ciph_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.cs.sub_right (by rw [stOf_w64 L.fw] at *; exact Lay.stSub (by decide))) G.rounds]
    exact h.o.ciph
  refine ⟨OEnv.frameT G D h.o f (by rw [g.env.ebp, h.o.env.ebp]) (by rw [g.env.esi, h.o.env.esi])
      (by rw [g.env.esp, h.o.env.esp]) (by rw [g.rd, rd₁]) (by rw [g.wr, wr₁]), h.ix, ?_, ?_, ?_, fun d hd => ?_⟩
  · have hX : ∀ r ∈ [(⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 48, 16⟩ : Region),
        ⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 64, 16 * 1⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 512, 2048⟩, below p.1 32],
        (⟨w64 (p.2 8) + BitVec.ofNat 64 auxO, 4⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [st_eq G]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · rw [st_eq G]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm
    rw [slotv_eq, slot_frame gf hX, slot_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hX _ (by simp), ← slotv_eq]
    exact h.aux
  · have hX : ∀ r ∈ [(⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 48, 16⟩ : Region),
        ⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 64, 16 * 1⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 512, 2048⟩, below p.1 32],
        (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact G.d_w.sub_right (region_sub_trans (sW (by decide)) (Lay.wSub (by decide)))
      · exact G.d_w.sub_right (region_sub_trans (sW (by decide)) (Lay.wSub (by decide)))
      · exact G.d_w.sub_right (Lay.wSub (by decide))
      · exact G.k_d.symm
    rw [two (X := ⟨w64 (p.2 6), (p.2 7).toNat⟩) (by have := G.fd; omega_using []) hX rfl]; exact h.data
  · have tA : ∀ {A : Region}, A.Sub ⟨w64 (p.2 8), 2560⟩ →
        (⟨w64 T, 16 * ((p.2 7).toNat / 16)⟩ : Region).Disjoint A :=
      fun hA => (D.w_t.sub_left hA).symm.sub_left (Region.sub_prefix hk)
    rw [bytesAt_frame gf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact tA (region_sub_trans (sW (by decide)) (Lay.wSub (by decide)))
        · exact tA (region_sub_trans (sW (by decide)) (Lay.wSub (by decide)))
        · exact tA (Lay.wSub (by decide))
        · exact (D.k_t.sub_right (Region.sub_prefix hk)).symm) (by have := D.fT; omega_using []),
      bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact tA (region_sub_trans (sW (by decide)) (Lay.wSub (by decide)))) (by have := D.fT; omega_using [])]
    exact h.whole
  · rw [ciph₁] at hks
    obtain t := (Proof.Gcm.ctr_tail h.ctr (by omega_using []) hks hcb (d := d) (by omega_using [hd]) (by omega_using [h0, hd])).1
    rwa [hd] at t

omit D in
/-- `tailRegs`: the keystream block in `edx`, the last bytes in `dst` in `edi`
and in the data in `esi`, and their number in `ecx`. -/
theorem tailRegs_ok {s₀ s : State} (h : OEnv p s₀ s) (hT : s.mem.readW (w64 p.1) 32 = T)
    (hr : InRegions (s.rd ++ s.wr) (w64 p.1) 4) :
    ∃ s', runBlock isa tailRegs s = some s' ∧ s'.gpr .edx = stOf (p.2 8) + BitVec.ofNat 32 64 ∧
      s'.gpr .edi = T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16)) ∧
      s'.gpr .esi = p.2 6 + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16)) ∧
      s'.gpr .ecx = BitVec.ofNat 32 ((p.2 7).toNat % 16) ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have L := G.L
  have hd := h.dataO
  have hn := h.lenO
  rw [← ofNat_toNat32 (p.2 7)] at hn
  obtain hlt := (p.2 7).isLt
  obtain hand := and15 (BitVec.ofNat 32 (p.2 7).toNat)
  rw [toNat_ofNat32 hlt] at hand
  obtain h16 : BitVec.ofNat 32 (p.2 7).toNat - BitVec.ofNat 32 ((p.2 7).toNat % 16) =
      BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) hlt]; congr 1; omega_using []
  obtain hr' : InRegions (s.rd ++ s.wr) (w64 (s.gpr .esp + BitVec.ofNat 32 0)) 4 := by
    rw [add_zero32, h.env.esp]; exact hr
  obtain hT' : s.mem.readW (w64 (s.gpr .esp + BitVec.ofNat 32 0)) 32 = T := by rw [add_zero32, h.env.esp]; exact hT
  refine ⟨_, by xrun [tailRegs, h.env.ebp, L.aW, h.env.wIn', hd, hn, hr', hT'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · regs [h.env.esi]
  · regs [hand, h16]
  · regs [hand, h16]
  · regs [hand]
  all_goals first | regs [] | mems []

/-- After `tailRegs`, from the state `u` after the keystream block. -/
structure XR (p : BitVec 32 × (Nat → BitVec 32)) (T : BitVec 32) (s₀ u s : State) : Prop where
  ks : KS p T s₀ u
  mem : s.mem = u.mem
  rd : s.rd = u.rd
  wr : s.wr = u.wr
  ebp : s.gpr .ebp = u.gpr .ebp
  esp : s.gpr .esp = u.gpr .esp
  edx : s.gpr .edx = stOf (p.2 8) + BitVec.ofNat 32 64
  edi : s.gpr .edi = T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))
  esi : s.gpr .esi = p.2 6 + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))
  ecx : s.gpr .ecx = BitVec.ofNat 32 ((p.2 7).toNat % 16)

omit G in
/-- The last bytes of the destination, at `16 k`, within it. -/
theorem tl_sub : Region.Sub ⟨w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))), (p.2 7).toNat % 16⟩
    ⟨w64 T, (p.2 7).toNat⟩ := by
  by_cases h0 : (p.2 7).toNat % 16 = 0
  · intro a h; simp only [Region.Contains] at h; omega
  rw [w64_add (by have := D.fT; omega_using [h0, this])]; exact Offset.sub_base _ (by omega_using [])

omit G in
/-- The first `16 k` bytes of the destination are apart from its last bytes. -/
theorem wh_tl : (⟨w64 T, 16 * ((p.2 7).toNat / 16)⟩ : Region).Disjoint
    ⟨w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))), (p.2 7).toNat % 16⟩ := by
  by_cases h0 : (p.2 7).toNat % 16 = 0
  · intro a _ h; simp only [Region.Contains] at h; omega_using [h0, h]
  rw [w64_add (by have := D.fT; omega_using [h0, this])]; exact split_disj (by have := D.fT; omega_using [])

omit D in
theorem regs_pc : Pc (KS p T) (.block tailRegs) (fun s₀ s => ∃ u, XR p T s₀ u s) :=
  Pc.taint [.ebp, .esi, .esp] (fun s₀ s h => by
      obtain ⟨s', run, dx, di, si, cx, bp, sp, m, rd, wr⟩ :=
        tailRegs_ok G h.o (IX.retT (q := ((p, T), true)) h.ix h.o) (IX.retIn (q := ((p, T), true)) h.ix h.o)
      exact WP.of_runBlock ⟨s', run, s, ⟨h, m, rd, wr, bp, sp, dx, di, si, cx⟩⟩)
    (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.o.env.ebp, h₂.o.env.ebp]
      · rw [h₁.o.env.esi, h₂.o.env.esi]
      · rw [h₁.o.env.esp, h₂.o.env.esp]) (by taint_decide)

/-- The last bytes XORed from the data into `dst` (`xorLoopG` out of place). -/
theorem xor_pc (h0 : (p.2 7).toNat % 16 ≠ 0) :
    Pc (fun s₀ s => ∃ u, XR p T s₀ u s) (xorLoopG true) (fun s₀ s' => ∃ u v, XR p T s₀ u v ∧
      XorPostG true v (stOf (p.2 8) + BitVec.ofNat 32 64) (p.2 6 + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16)))
        (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))) ((p.2 7).toNat % 16) s') := by
  have L := G.L
  obtain hk : 16 * ((p.2 7).toNat / 16) ≤ (p.2 7).toNat := Nat.mul_div_le _ _
  have hfT := D.fT
  have hfd := G.fd
  refine Pc.taint [.edi, .edx, .ecx, .esi] (fun s₀ v ⟨u, h⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.edi, h₂.edi]
      · rw [h₁.edx, h₂.edx]
      · rw [h₁.ecx, h₂.ecx]
      · rw [h₁.esi, h₂.esi]) (by taint_decide)
  obtain eT : w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))) =
      w64 T + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16)) := w64_add (by omega_using [h0, hfT])
  obtain eS : w64 (p.2 6 + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))) =
      w64 (p.2 6) + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16)) := w64_add (by omega_using [h0, hfd])
  obtain eK := L.aS (o := 64) (by decide)
  have o := h.ks.o
  obtain dW : Covers [⟨w64 T, (p.2 7).toNat⟩] v.wr := by rw [h.wr, o.wr]; exact IX.dW h.ks.ix
  refine WP.mono (xorLoopG_ok true v ⟨h.edx, h.edi, h.esi, (fun e => nomatch e), h.ecx, by omega_using [h0], by omega_using [],
    by rw [L.nS (by decide)]; have := L.fs; omega_using [this], by rw [toNat_add32 (by omega_using [h0, hfd])]; omega_using [hfd],
    by rw [toNat_add32 (by omega_using [h0, hfT])]; omega_using [hfT], ?_, ?_, ?_, ?_, .inr ?_⟩) fun s' x => ⟨u, v, h, x⟩
  · rw [eK, h.rd, h.wr]; exact covers_left (o.env.stC (by omega_using []))
  · rw [eS, h.rd, h.wr]; exact covers_off o.dIn (by omega_using []) (by omega_using [])
  · rw [eT]; exact covers_off dW (by omega_using []) (by omega_using [])
  · rw [eK, eT]
    exact ((D.w_t.sub_left (by rw [st_eq G]; exact Lay.wSub (by omega_using []))).sub_right
      (Offset.sub_base _ (by omega_using [])))
  · rw [eS, eT]
    exact (D.d_t.sub_left (Offset.sub_base _ (by omega_using []))).sub_right (Offset.sub_base _ (by omega_using []))

/-- `esi` the state again, and the plaintext at the destination. -/
theorem fin_pc (h0 : (p.2 7).toNat % 16 ≠ 0) :
    Pc (fun s₀ s' => ∃ u v, XR p T s₀ u v ∧
      XorPostG true v (stOf (p.2 8) + BitVec.ofNat 32 64) (p.2 6 + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16)))
        (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))) ((p.2 7).toNat % 16) s')
      (.block [.mov .esi (.reg .ebp), .alu .add .esi (imm stO)]) (OD BodyTo dstOf outTo fbTo ((p, T), true)) := by
  have L := G.L
  obtain hk : 16 * ((p.2 7).toNat / 16) ≤ (p.2 7).toNat := Nat.mul_div_le _ _
  have hfT := D.fT
  refine Pc.taint [.ebp] (fun s₀ s ⟨u, v, h, x⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, x₁⟩ ⟨_, _, h₂, x₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [x₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebp,
        x₂.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₂.ebp,
        h₁.ks.o.env.ebp, h₂.ks.o.env.ebp]) (by taint_decide)
  have o := h.ks.o
  obtain bp : s.gpr .ebp = p.2 8 := by
    rw [x.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.ebp, o.env.ebp]
  obtain sp : s.gpr .esp = u.gpr .esp := by
    rw [x.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.esp]
  refine WP.of_runBlock ⟨_, by xrun [bp], ?_⟩
  obtain eT : w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))) =
      w64 T + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16)) := w64_add (by omega_using [h0, hfT])
  obtain hxl := length_xorBytes u.mem (w64 (p.2 6 + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))))
    (w64 (stOf (p.2 8) + BitVec.ofNat 32 64)) ((p.2 7).toNat % 16)
  obtain fw : Frame [⟨w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))), (p.2 7).toNat % 16⟩] u.mem s.mem := by
    rw [x.mem, h.mem]; exact writeBytes_frame' _ hxl
  obtain tl : ∀ {X : Region}, X.Disjoint ⟨w64 T, (p.2 7).toNat⟩ →
      ∀ r ∈ [(⟨w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))), (p.2 7).toNat % 16⟩ : Region)],
        X.Disjoint r := fun hX r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hX.sub_right (tl_sub D)
  refine ⟨OEnv.frameT G D o (fw.sub fun r hr => ?_) (by regs [bp, o.env.ebp])
      (by regs [bp, o.env.esi]) (by regs [sp]) (by mems [x.rd, h.rd]) (by mems [x.wr, h.wr]), h.ks.ix, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., tl_sub D⟩
  · mems [slotv_eq]
    rw [slot_frame fw (tl (D.w_t.sub_left (Lay.wSub (by decide)))), ← slotv_eq]; exact h.ks.aux
  · show bytesAt s.mem (w64 T) (p.2 7).toNat =
      gctr (ciphP p s₀) (icbP p s₀) (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat)
    obtain spl : ∀ (m : Mem) (a : Addr), bytesAt m a (p.2 7).toNat =
        bytesAt m a (16 * ((p.2 7).toNat / 16)) ++
          bytesAt m (a + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16))) ((p.2 7).toNat % 16) := fun m a => by
      rw [← bytesAt_add]; congr 1; omega_using []
    obtain hw : bytesAt s.mem (w64 T) (16 * ((p.2 7).toNat / 16)) = bytesAt u.mem (w64 T) (16 * ((p.2 7).toNat / 16)) :=
      bytesAt_frame fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact wh_tl D) (by omega_using [])
    obtain ws := bytesAt_writeBytes_self u.mem (w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))))
      (xorBytes u.mem (w64 (p.2 6 + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))))
        (w64 (stOf (p.2 8) + BitVec.ofNat 32 64)) ((p.2 7).toNat % 16)) (by rw [hxl]; omega_using [])
    rw [hxl] at ws
    obtain src := congrArg (List.drop (16 * ((p.2 7).toNat / 16))) h.ks.data
    rw [bytesAt_drop _ _ hk, bytesAt_drop _ _ hk, show (p.2 7).toNat - 16 * ((p.2 7).toNat / 16) =
      (p.2 7).toNat % 16 by omega_using []] at src
    obtain kb := h.ks.kb (bytesAt u.mem (w64 (p.2 6) + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16)))
      ((p.2 7).toNat % 16)) (length_bytesAt _ _ _)
    rw [src] at kb
    obtain tailEq : bytesAt s.mem (w64 T + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16))) ((p.2 7).toNat % 16) =
        xorKs (ciphP p s₀) (icbP p s₀) (16 * ((p.2 7).toNat / 16))
          (bytesAt s₀.mem (w64 (p.2 6) + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16))) ((p.2 7).toNat % 16)) := by
      rw [← eT, x.mem, h.mem, ws, xorBytes, w64_add (show (p.2 6).toNat + 16 * ((p.2 7).toNat / 16) < 2 ^ 32 by
        have := G.fd; omega_using [h0, this]), L.aS (o := 64) (by decide), src]
      exact kb
    rw [spl, spl, Proof.Gcm.gctr_eq, Proof.Gcm.xorKs_append, length_bytesAt, Nat.zero_add, hw, h.ks.whole, tailEq]

end

/-- `decTo`: the data decrypted to the destination. -/
theorem decTo_pc (vg : GcmImpl) (q : OQ) (ht : q.2 = true) :
    Pc (OC BodyTo dstOf q) (decTo vg.callees ⟨vg.ctr.callee.name, vg.ctr.callee.code⟩)
      (OD BodyTo dstOf outTo fbTo q) := by
  obtain ⟨⟨p, T⟩, b⟩ := q
  dsimp only at ht
  subst ht
  by_cases hex : ∃ s₀ s, OC BodyTo dstOf ((p, T), true) s₀ s
  swap
  · exact Pc.vacuous fun a s h => hex ⟨a, s, h⟩
  obtain ⟨z, w, hz⟩ := hex
  obtain G : OL p := hz.ix.pre.op.ol rfl (by decide) hz.ix.pub
  obtain D : DL p T := IX.dl hz.ix
  unfold decTo
  have L := G.L
  refine Pc.seq (wholeTo_pc G D vg) (Pc.seq (Q := fun s₀ s => DW p T s₀ s ∧ s.zf = some (decide ((p.2 7).toNat % 16 = 0)))
    (Pc.taint [.ebp] (fun s₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)) ?_)
  · obtain ⟨s', run, _, zf, g, m, rd, wr⟩ := tailLen_ok G h.o
    refine WP.of_runBlock ⟨s', run, ⟨h.o.frame G (by rw [m]; exact Frame.refl _ _) (g _ (by decide))
      (g _ (by decide)) (g _ (by decide)) rd wr, h.ix, by rw [m]; exact h.aux, by rw [m]; exact h.data,
      by rw [m]; exact h.whole, h.ctr.congr (by rw [m]) (by rw [m])⟩, zf⟩
  refine Pc.ite (decide ((p.2 7).toNat % 16 = 0)) (fun _ _ h => h.2) (fun hb => ?_) (fun hb => ?_)
  · have h0 : (p.2 7).toNat % 16 = 0 := by simpa using hb
    refine Pc.mono Pc.nil (fun _ _ h => h) fun s₀ s ⟨h, _⟩ => ⟨h.o, h.ix, h.aux, ?_⟩
    show bytesAt s.mem (w64 T) (p.2 7).toNat =
      gctr (ciphP p s₀) (icbP p s₀) (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat)
    have hw := h.whole
    rw [show 16 * ((p.2 7).toNat / 16) = (p.2 7).toNat by omega_using [h0]] at hw
    rw [Proof.Gcm.gctr_eq]; exact hw
  · have h0 : (p.2 7).toNat % 16 ≠ 0 := by simpa using hb
    exact Pc.seq (Pc.mono (ks_pc G D vg h0) (fun _ _ h => h.1) fun _ _ h => h)
      (Pc.seq (regs_pc G) (Pc.seq (xor_pc G D h0) (fin_pc G D h0)))

end VG.Proof.AesGcm.X86.OpenTo

end

end

/-!
# AES-GCM decryption out of place on x86: `vg_aes_gcm_open_to`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_to` runs
`open`'s body (`Open.lean`) in a frame of 48 bytes of its own (`Open.openTo`):
the entry copies `open`'s arguments into it, the data being `src`, and `dst`
into the word at its `esp` (`frameArgs_ok`), and the body runs in the mode
out of place (`toMode`, `Dec.lean`): the data decrypted to `dst`, or `dst`
zeroed. With its working space as an argument, it is proven against the
contract the frame of `withStackScratch` needs (`openTo_verified`), and so,
in that frame, against `Proof.AesGcm.openToRoundsContract` (`openTo_framed`),
from which `Spec.Gcm.openToContract` follows (`Proof.AesGcm.openTo_keyed`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.OpenTo

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.Open
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)

/-! ## The mode out of place -/

/-- `open`'s body out of place: the data decrypted to `dst`, the word at
`esp`, and `dst` zeroed if the tag length is not allowed or the tag is
wrong. -/
def toMode (vg : GcmImpl) : OMode vg where
  Pre := BodyTo
  op := fun _ h => h.op
  tg := fun _ h => h.tg
  x := dstOf
  out := outTo
  fb := fbTo
  out_mem := fun _ _ _ _ h => by simp only [outTo, h]
  bad := wipe
  fail := wipe
  dec := decTo vg.callees ⟨vg.ctr.callee.name, vg.ctr.callee.code⟩
  hbad := fun q _ => wipeBad_pc q
  hfail := fun q hf => wipeFail_pc q hf
  hdec := fun q ht => decTo_pc vg q ht

/-! ## The contract -/

/-- `vg_aes_gcm_open_to(ctx, rounds, nonce, nonce_len, aad, aad_len, src, len, dst, dst_len, tag, tag_len, work)`. -/
def toPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let nonce : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  let aad : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
  let src : Region := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩
  let dst : Region := ⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩
  let tag : Region := ⟨(arg s 10).setWidth 64, (arg s 11).toNat⟩
  let scr : Region := ⟨(arg s 12).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 52⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 80, 80⟩
  s.rd = [ctx, nonce, aad, src, tag] ∧ s.wr = [dst, scr, args] ∧
  ctx.Disjoint dst ∧ ctx.Disjoint scr ∧ nonce.Disjoint dst ∧ nonce.Disjoint scr ∧ aad.Disjoint dst ∧
  aad.Disjoint scr ∧ src.Disjoint dst ∧ src.Disjoint scr ∧ dst.Disjoint tag ∧ dst.Disjoint scr ∧
  dst.Disjoint args ∧ tag.Disjoint scr ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint src ∧ ret.Disjoint dst ∧
  ret.Disjoint tag ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint nonce ∧ stack.Disjoint aad ∧ stack.Disjoint src ∧
  stack.Disjoint dst ∧ stack.Disjoint tag ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
  (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧ (arg s 10).toNat + (arg s 11).toNat ≤ 2 ^ 32 ∧
  (arg s 12).toNat + 2560 ≤ 2 ^ 32 ∧ 80 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 56 ≤ 2 ^ 32 ∧
  roundsOk s 1 ∧ (arg s 9).toNat = (arg s 7).toNat

/-- What `open_to` computes. -/
abbrev toRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (ctxH s.mem ((arg s 0).setWidth 64))
    (arg s 11).toNat (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
    (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat) (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
    (bytesAt s.mem ((arg s 10).setWidth 64) (arg s 11).toNat)

def toX86 : Contract isa where
  pre := toPre
  post s s' :=
    match toRes s with
    | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧
        bytesAt s'.mem ((arg s 8).setWidth 64) (arg s 7).toNat = pt
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
        bytesAt s'.mem ((arg s 8).setWidth 64) (arg s 7).toNat = List.replicate (arg s 7).toNat 0
  pub s₁ s₂ := pubN 13 s₁ s₂ ∧ (toRes s₁).isSome = (toRes s₂).isSome

/-- What the frame of `withStackScratch` needs of the code: the shared contract
with the working space as a last argument, whatever it holds, and 80 bytes of
stack (the frame of 48 and the calls' 32). -/
abbrev toScratchK : Contract isa :=
  Sig.scratchContract X86.abi Spec.Gcm.openToSig "work" .u64 320 (Spec.Gcm.openToPre X86.abi.ptrBits)
    (Proof.AesGcm.openToRoundsPost X86.abi.ptrBits) true 80 (some (Spec.Gcm.openToLeak X86.abi.ptrBits))

theorem to_pre : ∀ s, toScratchK.pre s → toX86.pre s := by
  sig_implies_pre [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
    pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

/-! ## The frame's entry -/

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 104 ≤ 2 ^ 32)
include hP

theorem aP {d : Nat} (hd : d < 104) : w64 (P + BitVec.ofNat 32 d) = w64 P + BitVec.ofNat 64 d :=
  w64_add (by omega_arith)

/-- A word of the frame (or above it) after a write of another. -/
theorem rdw {d e : Nat} (v : BitVec 32) (hd : d + 4 ≤ 104) (he : e + 4 ≤ 104) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (w64 (P + BitVec.ofNat 32 e)) v).readW (w64 (P + BitVec.ofNat 32 d)) 32 =
      m.readW (w64 (P + BitVec.ofNat 32 d)) 32 := by
  rw [aP hP (by omega_arith), aP hP (by omega_arith)]
  exact Mem.readW_writeW_sep (Offset.sep _ h (by omega_arith) (by omega_arith)) (by decide)

theorem rdw0 {e : Nat} (v : BitVec 32) (he : e + 4 ≤ 104) (h : 4 ≤ e) :
    (m.writeW (w64 (P + BitVec.ofNat 32 e)) v).readW (w64 P) 32 = m.readW (w64 P) 32 := by
  have := rdw hP (m := m) (d := 0) v (by decide) he (.inl h)
  rwa [add_zero32] at this

theorem rd0w {d : Nat} (v : BitVec 32) (hd : d + 4 ≤ 104) (h : 4 ≤ d) :
    (m.writeW (w64 P) v).readW (w64 (P + BitVec.ofNat 32 d)) 32 = m.readW (w64 (P + BitVec.ofNat 32 d)) 32 := by
  have := rdw hP (m := m) (d := d) (e := 0) v hd (by decide) (.inr h)
  rwa [add_zero32] at this

omit hP in
theorem rds (v : BitVec 32) (a : Addr) : (m.writeW a v).readW a 32 = v :=
  Mem.readW_writeW_self m a 4 v (by decide)

end

theorem frameArgs_eq : frameArgs =
    [.mov .eax (.mem (at_ .esp 84)), .store (at_ .esp 0) .eax,
      .mov .eax (.mem (at_ .esp 52)), .store (at_ .esp 4) .eax, .mov .eax (.mem (at_ .esp 56)), .store (at_ .esp 8) .eax,
      .mov .eax (.mem (at_ .esp 60)), .store (at_ .esp 12) .eax, .mov .eax (.mem (at_ .esp 64)), .store (at_ .esp 16) .eax,
      .mov .eax (.mem (at_ .esp 68)), .store (at_ .esp 20) .eax, .mov .eax (.mem (at_ .esp 72)), .store (at_ .esp 24) .eax,
      .mov .eax (.mem (at_ .esp 76)), .store (at_ .esp 28) .eax, .mov .eax (.mem (at_ .esp 80)), .store (at_ .esp 32) .eax,
      .mov .eax (.mem (at_ .esp 92)), .store (at_ .esp 36) .eax, .mov .eax (.mem (at_ .esp 96)), .store (at_ .esp 40) .eax,
      .mov .eax (.mem (at_ .esp 100)), .store (at_ .esp 44) .eax] := rfl

/-- The memory after the frame's entry, at the frame `P`: `dst` (at `P + 84`)
at `P`, and our arguments but `dst` and `dst_len` (at `P + 52` … `P + 80`,
`P + 92` … `P + 100`) at `P + 4` … `P + 44`. -/
def fMem (m : Mem) (P : BitVec 32) : Mem :=
  let w (m : Mem) (d : Nat) (v : BitVec 32) := m.writeW (w64 (P + BitVec.ofNat 32 d)) v
  let r (d : Nat) := m.readW (w64 (P + BitVec.ofNat 32 d)) 32
  w (w (w (w (w (w (w (w (w (w (w (m.writeW (w64 P) (r 84)) 4 (r 52)) 8 (r 56)) 12 (r 60)) 16 (r 64))
    20 (r 68)) 24 (r 72)) 28 (r 76)) 32 (r 80)) 36 (r 92)) 40 (r 96)) 44 (r 100)

theorem frameArgs_ok (a : State) (hP : (a.gpr .esp).toNat + 104 ≤ 2 ^ 32)
    (hw : ∀ d, d + 4 ≤ 48 → InRegions a.wr (w64 (a.gpr .esp + BitVec.ofNat 32 d)) 4)
    (hr : ∀ d, 52 ≤ d → d + 4 ≤ 104 → InRegions (a.rd ++ a.wr) (w64 (a.gpr .esp + BitVec.ofNat 32 d)) 4) :
    ∃ e, runBlock isa frameArgs a = some e ∧ e.mem = fMem a.mem (a.gpr .esp) ∧
      (∀ r, r ≠ .eax → e.gpr r = a.gpr r) ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  obtain hw0 : InRegions a.wr (w64 (a.gpr .esp)) 4 := by simpa only [add_zero32] using hw 0 (by decide)
  refine ⟨_, by
    xrun [frameArgs_eq, hw0, hw 4 (by decide), hw 8 (by decide), hw 12 (by decide), hw 16 (by decide),
      hw 20 (by decide), hw 24 (by decide), hw 28 (by decide), hw 32 (by decide), hw 36 (by decide),
      hw 40 (by decide), hw 44 (by decide), hr 52 (by decide) (by decide), hr 56 (by decide) (by decide),
      hr 60 (by decide) (by decide), hr 64 (by decide) (by decide), hr 68 (by decide) (by decide),
      hr 72 (by decide) (by decide), hr 76 (by decide) (by decide), hr 80 (by decide) (by decide),
      hr 84 (by decide) (by decide), hr 92 (by decide) (by decide), hr 96 (by decide) (by decide),
      hr 100 (by decide) (by decide), add_zero32, rdw hP, rdw0 hP, rd0w hP], ?_, fun r h => ?_, ?_, ?_⟩
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rfl
  · simp [gpr_setMem, gpr_setReg, gpr_arithFlags, h]
  · simp only [rd_setMem, rd_setReg, rd_arithFlags]
  · simp only [wr_setMem, wr_setReg, wr_arithFlags]

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 104 ≤ 2 ^ 32)
include hP

/-- The entry writes only the frame. -/
theorem fMem_frame : Frame [⟨w64 P, 48⟩] m (fMem m P) := by
  have c (d : Nat) (hd : d + 4 ≤ 48) : (⟨w64 P, 48⟩ : Region).Contains (w64 (P + BitVec.ofNat 32 d)) 4 := by
    rw [aP hP (by omega_arith)]; exact Offset.contains_base _ hd (by omega_arith)
  obtain c0 : (⟨w64 P, 48⟩ : Region).Contains (w64 P) 4 := by simp [Region.Contains]
  obtain hm := List.mem_singleton_self (⟨w64 P, 48⟩ : Region)
  unfold fMem; dsimp only
  refine Frame.writeW ?_ hm _ (c 44 (by decide)); refine Frame.writeW ?_ hm _ (c 40 (by decide))
  refine Frame.writeW ?_ hm _ (c 36 (by decide)); refine Frame.writeW ?_ hm _ (c 32 (by decide))
  refine Frame.writeW ?_ hm _ (c 28 (by decide)); refine Frame.writeW ?_ hm _ (c 24 (by decide))
  refine Frame.writeW ?_ hm _ (c 20 (by decide)); refine Frame.writeW ?_ hm _ (c 16 (by decide))
  refine Frame.writeW ?_ hm _ (c 12 (by decide)); refine Frame.writeW ?_ hm _ (c 8 (by decide))
  refine Frame.writeW ?_ hm _ (c 4 (by decide)); refine Frame.writeW ?_ hm _ c0
  exact Frame.refl _ _

/-- The words of the frame after the entry. -/
theorem fMem_words :
    let e := fMem m P
    let r (m : Mem) (d : Nat) := m.readW (w64 (P + BitVec.ofNat 32 d)) 32
    e.readW (w64 P) 32 = r m 84 ∧ r e 4 = r m 52 ∧ r e 8 = r m 56 ∧ r e 12 = r m 60 ∧ r e 16 = r m 64 ∧
      r e 20 = r m 68 ∧ r e 24 = r m 72 ∧ r e 28 = r m 76 ∧ r e 32 = r m 80 ∧ r e 36 = r m 92 ∧
      r e 40 = r m 96 ∧ r e 44 = r m 100 := by
  simp (disch := first | decide | omega_arith) only [fMem, rdw hP, rdw0 hP, rd0w hP, rds]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial⟩

end

/-! ## The precondition, by name -/

section
variable (s : State)

/-- The frame. -/
abbrev Pf : BitVec 32 := s.gpr .esp - BitVec.ofNat 32 48

/-- The public data of the body's run: `open`'s arguments, `W` at 8 and
`tag` at 10, at the frame. -/
def pubTo : BitVec 32 × (Nat → BitVec 32) :=
  (Pf s, fun k => if k < 11 then arg s (if k = 8 then 12 else if k = 9 then 11 else k) else 0)

end

/-- `toPre`, by name, with the stack as `below`. -/
structure TP (s : State) : Prop where
  rd : s.rd = [⟨w64 (arg s 0), 256⟩, ⟨w64 (arg s 2), (arg s 3).toNat⟩, ⟨w64 (arg s 4), (arg s 5).toNat⟩,
    ⟨w64 (arg s 6), (arg s 7).toNat⟩, ⟨w64 (arg s 10), (arg s 11).toNat⟩]
  wr : s.wr = [⟨w64 (arg s 8), (arg s 7).toNat⟩, ⟨w64 (arg s 12), 2560⟩, ⟨argAddr s 0, 52⟩]
  c_t : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  c_w : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  n_t : (⟨w64 (arg s 2), (arg s 3).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  n_w : (⟨w64 (arg s 2), (arg s 3).toNat⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  a_t : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  a_w : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  d_t : (⟨w64 (arg s 6), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  d_w : (⟨w64 (arg s 6), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  t_g : (⟨w64 (arg s 8), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 10), (arg s 11).toNat⟩
  t_w : (⟨w64 (arg s 8), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  g_w : (⟨w64 (arg s 10), (arg s 11).toNat⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  k_c : (below (s.gpr .esp) 80).Disjoint ⟨w64 (arg s 0), 256⟩
  k_n : (below (s.gpr .esp) 80).Disjoint ⟨w64 (arg s 2), (arg s 3).toNat⟩
  k_a : (below (s.gpr .esp) 80).Disjoint ⟨w64 (arg s 4), (arg s 5).toNat⟩
  k_d : (below (s.gpr .esp) 80).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  k_t : (below (s.gpr .esp) 80).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  k_g : (below (s.gpr .esp) 80).Disjoint ⟨w64 (arg s 10), (arg s 11).toNat⟩
  k_w : (below (s.gpr .esp) 80).Disjoint ⟨w64 (arg s 12), 2560⟩
  r_t : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  r_w : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  r_a : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  fc : (arg s 0).toNat + 256 ≤ 2 ^ 32
  fn : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  fa : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  fd : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  ft : (arg s 8).toNat + (arg s 7).toNat ≤ 2 ^ 32
  fg : (arg s 10).toNat + (arg s 11).toNat ≤ 2 ^ 32
  fw : (arg s 12).toNat + 2560 ≤ 2 ^ 32
  sp : 80 ≤ (s.gpr .esp).toNat
  hi : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32
  rounds : roundsOk s 1

theorem TP.of {s : State} (h : toPre s) : TP s := by
  simp only [toPre] at h
  obtain ⟨hrd, hwr, c_t, c_w, n_t, n_w, a_t, a_w, d_t, d_w, t_g, t_w, -, g_w, -, -, -, -, -, r_t, -, r_w, r_a, k_c,
    k_n, k_a, k_d, k_t, k_g, k_w, -, fc, fn, fa, fd, ft, fg, fw, sp, hi, hR, hl⟩ := h
  rw [ofNat_lit, below_eq sp] at k_c k_n k_a k_d k_t k_g k_w
  rw [hl] at hwr c_t n_t a_t d_t t_g t_w k_t r_t ft
  exact ⟨hrd, hwr, c_t, c_w, n_t, n_w, a_t, a_w, d_t, d_w, t_g, t_w, g_w, k_c, k_n, k_a, k_d, k_t, k_g, k_w, r_t, r_w,
    r_a, fc, fn, fa, fd, ft, fg, fw, sp, hi, hR⟩

namespace TP
variable {s : State} (h : TP s)
include h

theorem pN : (Pf s).toNat = (s.gpr .esp).toNat - 48 := sub_toNat (by have := h.sp; omega_using [this])

theorem hP : (Pf s).toNat + 104 ≤ 2 ^ 32 := by rw [h.pN]; have := h.sp; have := h.hi; omega_using [this]

/-- Our argument `i`, above the frame. -/
theorem argA (i : Nat) : argAddr s i = w64 (Pf s + BitVec.ofNat 32 (52 + 4 * i)) := by
  have := h.sp
  simp only [argAddr, Pf]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using []

theorem argOf {j : Nat} {v : BitVec 32}
    (hv : s.mem.readW (w64 (Pf s + BitVec.ofNat 32 (52 + 4 * j))) 32 = v) : arg s j = v := by
  rw [← hv]; show s.mem.readW (argAddr s j) 32 = _; rw [h.argA j]

/-- The frame and the words in it, within the stack below `esp`. -/
theorem frame_sub {d n : Nat} (hd : d + n ≤ 48) :
    Region.Sub ⟨w64 (Pf s) + BitVec.ofNat 64 d, n⟩ (below (s.gpr .esp) 80) :=
  region_sub_trans (Offset.sub_base _ hd) (below_sub (by decide) h.sp)

theorem frame_sub0 {n : Nat} (hn : n ≤ 48) : Region.Sub ⟨w64 (Pf s), n⟩ (below (s.gpr .esp) 80) :=
  region_sub_trans (Region.sub_prefix hn) (below_sub (by decide) h.sp)

/-- The stack the body's calls use, within ours. -/
theorem stk_sub : Region.Sub (below (Pf s) 32) (below (s.gpr .esp) 80) :=
  below_inner (by decide) h.sp

/-- A region apart from the stack below `esp` is apart from the frame. -/
theorem frameDisj {X : Region} (hX : (below (s.gpr .esp) 80).Disjoint X) :
    ∀ r ∈ [(⟨w64 (Pf s), 48⟩ : Region)], X.Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact (hX.sub_left (h.frame_sub0 (Nat.le_refl _))).symm

end TP

/-- What the entry leaves: the frame's words as the body takes them. -/
structure Entered (s e : State) : Prop where
  esp : e.gpr .esp = Pf s
  gpr : ∀ r, r ≠ .eax → r ≠ .esp → e.gpr r = s.gpr r
  rd : e.rd = s.rd
  wr : e.wr = ⟨w64 (Pf s), 48⟩ :: s.wr
  frame : Frame [⟨w64 (Pf s), 48⟩] s.mem e.mem
  args : ∀ i, i < 11 → arg e i = arg s (if i = 8 then 10 else if i = 9 then 11 else if i = 10 then 12 else i)
  dst : e.mem.readW (w64 (Pf s)) 32 = arg s 8

theorem entered {s : State} (h : TP s) :
    WP isa (.block frameArgs) (allocFrame 48 s) (Entered s) := by
  have hP := h.hP
  obtain esp : (allocFrame 48 s).gpr .esp = Pf s := allocFrame_esp 48 s
  obtain hw : ∀ d, d + 4 ≤ 48 → InRegions (allocFrame 48 s).wr (w64 ((allocFrame 48 s).gpr .esp + BitVec.ofNat 32 d)) 4 :=
    fun d hd => by
      rw [esp, allocFrame_wr, aP hP (by omega_using [hd])]
      exact ⟨_, List.mem_cons_self .., Offset.contains_base _ hd (by omega_using [hd])⟩
  obtain hr : ∀ d, 52 ≤ d → d + 4 ≤ 104 →
      InRegions ((allocFrame 48 s).rd ++ (allocFrame 48 s).wr) (w64 ((allocFrame 48 s).gpr .esp + BitVec.ofNat 32 d)) 4 :=
    fun d h₁ h₂ => by
      refine in_left ⟨⟨argAddr s 0, 52⟩, ?_, ?_⟩
      · rw [allocFrame_wr, h.wr]; simp
      · rw [esp, h.argA 0, aP hP (by omega_using []), aP hP (by omega_using [h₂])]
        exact Offset.contains _ (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])
  obtain ⟨e, run, hm, hg, hrd, hwr⟩ := frameArgs_ok (allocFrame 48 s) (by rw [esp]; exact hP) hw hr
  refine WP.of_runBlock ⟨e, run, ?_⟩
  rw [esp] at hm
  obtain hw' := fMem_words (m := s.mem) hP
  simp only [allocFrame_mem] at hm
  obtain esp' : e.gpr .esp = Pf s := by rw [hg .esp (by decide), esp]
  obtain eA : ∀ i, arg e i = (fMem s.mem (Pf s)).readW (w64 (Pf s + BitVec.ofNat 32 (4 + 4 * i))) 32 := fun i => by
    simp only [arg, argAddr, esp', hm]
  refine ⟨esp', fun r h₁ h₂ => by rw [hg r h₁, allocFrame_gpr _ _ h₂], by rw [hrd, allocFrame_rd],
    by rw [hwr, allocFrame_wr], by rw [hm]; exact fMem_frame hP, fun i hi => ?_,
    (by rw [hm]; exact hw'.1.trans (h.argOf (j := 8) rfl).symm)⟩
  rw [eA]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw'.2.1.trans (h.argOf (j := 0) rfl).symm
  · exact hw'.2.2.1.trans (h.argOf (j := 1) rfl).symm
  · exact hw'.2.2.2.1.trans (h.argOf (j := 2) rfl).symm
  · exact hw'.2.2.2.2.1.trans (h.argOf (j := 3) rfl).symm
  · exact hw'.2.2.2.2.2.1.trans (h.argOf (j := 4) rfl).symm
  · exact hw'.2.2.2.2.2.2.1.trans (h.argOf (j := 5) rfl).symm
  · exact hw'.2.2.2.2.2.2.2.1.trans (h.argOf (j := 6) rfl).symm
  · exact hw'.2.2.2.2.2.2.2.2.1.trans (h.argOf (j := 7) rfl).symm
  · exact hw'.2.2.2.2.2.2.2.2.2.1.trans (h.argOf (j := 10) rfl).symm
  · exact hw'.2.2.2.2.2.2.2.2.2.2.1.trans (h.argOf (j := 11) rfl).symm
  · exact hw'.2.2.2.2.2.2.2.2.2.2.2.trans (h.argOf (j := 12) rfl).symm

namespace Entered
variable {s e : State} (h : TP s) (he : Entered s e)
include h he

omit h in
theorem a (i : Nat) (hi : i < 8) : arg e i = arg s i := by
  have := he.args i (by omega_using [hi])
  simpa only [show ¬(i = 8) by omega_using [hi], show ¬(i = 9) by omega_using [hi], show ¬(i = 10) by omega_using [hi], ↓reduceIte] using this

omit h in
theorem pub_eq : pubSw 11 8 e = pubTo s := by
  refine Prod.ext he.esp (funext fun k => ?_)
  simp only [pubSw, pubTo]
  by_cases hk : k < 11
  · simp only [hk, ↓reduceIte]
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact he.args _ (by decide)
  · simp only [hk, ↓reduceIte]

omit h in
theorem dst_eq : dstOf e = arg s 8 := by
  show e.mem.readW (w64 (e.gpr .esp)) 32 = _; rw [he.esp]; exact he.dst

omit h in
/-- The frame, readable and writable. -/
theorem frameIn : (⟨w64 (Pf s), 48⟩ : Region) ∈ e.rd ++ e.wr := by
  rw [he.wr]; exact List.mem_append_right _ (List.mem_cons_self ..)

theorem bodyTo : BodyTo e := by
  have hP := h.hP
  have pn := h.pN
  have hsp := h.sp
  have hhi := h.hi
  obtain a8 := he.args 8 (by decide)
  obtain a9 := he.args 9 (by decide)
  obtain a10 := he.args 10 (by decide)
  simp only [↓reduceIte, show (9 : Nat) ≠ 8 by decide, show (10 : Nat) ≠ 8 by decide,
    show (10 : Nat) ≠ 9 by decide] at a8 a9 a10
  obtain a0 := he.a 0 (by decide); have a1 := he.a 1 (by decide); have a2 := he.a 2 (by decide)
  obtain a3 := he.a 3 (by decide); have a4 := he.a 4 (by decide); have a5 := he.a 5 (by decide)
  obtain a6 := he.a 6 (by decide); have a7 := he.a 7 (by decide)
  have esp := he.esp
  obtain rdwr : ∀ r ∈ s.rd, r ∈ e.rd ++ e.wr := fun r hr => by rw [he.rd]; exact List.mem_append_left _ hr
  obtain wrwr : ∀ r ∈ s.wr, r ∈ e.wr := fun r hr => by rw [he.wr]; exact List.mem_cons_of_mem _ hr
  obtain eA0 : argAddr e 0 = w64 (Pf s) + BitVec.ofNat 64 4 := by
    show w64 (e.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)) = _; rw [esp]; exact aP hP (by decide)
  obtain fr : ∀ {d n : Nat}, d + n ≤ 48 → Covers [⟨w64 (Pf s) + BitVec.ofNat 64 d, n⟩] (e.rd ++ e.wr) :=
    fun hd => covers_off (covers_of_mem he.frameIn) hd (by decide)
  obtain kS : ∀ {X : Region}, (below (s.gpr .esp) 80).Disjoint X → (below (e.gpr .esp) 32).Disjoint X :=
    fun hX => by rw [esp]; exact hX.sub_left h.stk_sub
  obtain rS : ∀ {X : Region}, (below (s.gpr .esp) 80).Disjoint X → (⟨w64 (e.gpr .esp), 4⟩ : Region).Disjoint X :=
    fun hX => by rw [esp]; exact hX.sub_left (h.frame_sub0 (by decide))
  obtain aS : ∀ {X : Region}, (below (s.gpr .esp) 80).Disjoint X → X.Disjoint ⟨argAddr e 0, 4 * 11⟩ :=
    fun hX => by rw [eA0]; exact (hX.sub_left (h.frame_sub (d := 4) (n := 44) (by decide))).symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, aS (by rw [a6, a7]; exact h.k_d), aS (by rw [a10]; exact h.k_w),
    rS (by rw [a6, a7]; exact h.k_d), rS (by rw [a10]; exact h.k_w), kS (by rw [a0]; exact h.k_c),
    kS (by rw [a2, a3]; exact h.k_n), kS (by rw [a4, a5]; exact h.k_a), kS (by rw [a6, a7]; exact h.k_d),
    kS (by rw [a10]; exact h.k_w), by rw [a0]; exact h.fc, by rw [a2, a3]; exact h.fn, by rw [a4, a5]; exact h.fa,
    by rw [a6, a7]; exact h.fd, by rw [a10]; exact h.fw, by rw [esp, pn]; omega_using [hsp], by rw [esp, pn]; omega_using [],
    by show roundsOk e 1; simp only [roundsOk, a1]; exact h.rounds⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [a0]; exact covers_of_mem (rdwr _ (by rw [h.rd]; simp))
  · rw [a2, a3]; exact covers_of_mem (rdwr _ (by rw [h.rd]; simp))
  · rw [a4, a5]; exact covers_of_mem (rdwr _ (by rw [h.rd]; simp))
  · rw [a6, a7]; exact covers_of_mem (rdwr _ (by rw [h.rd]; simp))
  · rw [a10]; exact covers_of_mem (wrwr _ (by rw [h.wr]; simp))
  · rw [eA0]; exact fr (by decide)
  · rw [a0, a10]; exact h.c_w
  · rw [a2, a3, a10]; exact h.n_w
  · rw [a4, a5, a10]; exact h.a_w
  · rw [a6, a7, a10]; exact h.d_w
  · rw [a8, a9]; exact covers_of_mem (rdwr _ (by rw [h.rd]; simp))
  · rw [a8, a9]; exact h.fg
  · rw [a8, a9, a10]; exact h.g_w
  · rw [a8, a9]; exact kS h.k_g
  · rw [he.pub_eq, he.dst_eq]
    exact ⟨h.ft, h.c_t, h.n_t, h.a_t, h.d_t, h.t_g.symm, h.t_w.symm,
      h.k_t.sub_left (h.frame_sub0 (by decide)), h.k_t.sub_left h.stk_sub⟩
  · rw [he.dst_eq, a7]; exact covers_of_mem (wrwr _ (by rw [h.wr]; simp))
  · rw [esp]; exact covers_pre (covers_of_mem he.frameIn) (by decide) (by decide)

/-- What `open`'s body computes from the frame is what `open_to` computes. -/
theorem res : openRes e = toRes s := by
  have hf := he.frame
  have hR := h.rounds
  obtain a0 := he.a 0 (by decide); have a1 := he.a 1 (by decide); have a2 := he.a 2 (by decide)
  obtain a3 := he.a 3 (by decide); have a4 := he.a 4 (by decide); have a5 := he.a 5 (by decide)
  obtain a6 := he.a 6 (by decide); have a7 := he.a 7 (by decide)
  obtain a8 := he.args 8 (by decide)
  obtain a9 := he.args 9 (by decide)
  simp only [↓reduceIte, show (9 : Nat) ≠ 8 by decide] at a8 a9
  obtain hc : ciphOf e.mem (arg s 0) (arg s 1).toNat = ciphOf s.mem (arg s 0) (arg s 1).toNat :=
    ciph_frame hf (h.frameDisj h.k_c) hR
  simp only [openRes, toRes, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  rw [show ctxCiph e.mem (w64 (arg s 0)) (arg s 1).toNat = ctxCiph s.mem (w64 (arg s 0)) (arg s 1).toNat from hc,
    show ctxH e.mem (w64 (arg s 0)) = ctxH s.mem (w64 (arg s 0)) from by
      rw [ctxH_eq, ctxH_eq, blockAt_frame hf (h.frameDisj (h.k_c.sub_right (Lay.ctxSub (by decide))))],
    bytesAt_frame hf (h.frameDisj h.k_n) (by have := h.fn; omega_using []),
    bytesAt_frame hf (h.frameDisj h.k_d) (by have := h.fd; omega_using []),
    bytesAt_frame hf (h.frameDisj h.k_a) (by have := h.fa; omega_using []),
    bytesAt_frame hf (h.frameDisj h.k_g) (by have := h.fg; omega_using [])]

end Entered

/-! ## The frame -/

theorem noEsp_of {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

/-- A piece, with what its code may write: within the regions writable where
it starts and the stack below `esp` it uses (`Exec.frameSp`). -/
theorem Pc.frameSp {α : Sort _} {P Q : α → State → Prop} {c : Prog isa} (h : Pc P c Q) (hsp : NoSp c)
    (hd : ∀ a s, P a s → stackUse c ≤ (s.gpr .esp).toNat) :
    Pc P c fun a s' => Q a s' ∧ ∃ s, P a s ∧ Frame (s.wr ++ [below (s.gpr .esp) (stackUse c)]) s.mem s'.mem := by
  refine ⟨fun a s hs => ?_, h.ct⟩
  obtain ⟨t, s', he, hq⟩ := h.wp a s hs
  exact ⟨t, s', he, hq, s, hs, Exec.frameSp he hsp (hd a s hs)⟩

/-- A frame of `bytes` bytes, around a piece run from the state after the
allocation. -/
theorem Pc.frameAlloc {α : Sort _} {P Q : α → State → Prop} {bytes : Nat} {body : Prog isa}
    (h0 : 0 < bytes) (h1 : bytes < 4096) (h4 : bytes % 4 = 0) (hn : ∀ a s, P a s → bytes ≤ (s.gpr .esp).toNat)
    (hsp : NoSp body)
    (hb : Pc (fun a s₁ => ∃ s, P a s ∧ s₁ = allocFrame bytes s) body fun a s₂ => ∀ m u,
      Frame [⟨(s₂.gpr .esp).setWidth 64, bytes⟩] s₂.mem m → Q a { freed bytes s₂ with mem := m, unknowns := u }) :
    Pc P (.frame (.alloc bytes) body (.free bytes)) Q := by
  refine ⟨fun a s hs => WP.frameAlloc h0 h1 h4 (hn a s hs) hsp ?_, ?_⟩
  · obtain ⟨t, s₂, he, hq⟩ := hb.wp a _ ⟨s, hs, rfl⟩
    refine ⟨t, s₂, he, fun m u f => hq m u ?_⟩
    rw [Exec.gpr hsp he, allocFrame_esp]
    exact f
  exact RelCT.frameAlloc (RelCT.mono hb.ct (fun _ _ ⟨s₁, s₂, ⟨⟨a, h₁⟩, ⟨b, h₂⟩⟩, e₁, e₂⟩ =>
    ⟨⟨a, s₁, h₁, e₁⟩, ⟨b, s₂, h₂, e₂⟩⟩) fun _ _ _ => trivial)

section
variable (vg : GcmImpl)

/-- `vg_aes_ctr32_to`, of the implementations `vg`. -/
abbrev toFn : Fn := ⟨vg.ctr.callee.name, vg.ctr.callee.code⟩

theorem body_noEsp :
    (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg))).allInstrs (fun i => !Taint.clobbers i .esp) =
      true := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush,
    ghCall, ghash1, j0, j0hash, lens, oneAad, oneEntry, oneTag, recv, tag, tagLenOk, openBody, decTo, wholeTo,
    ctrToCall, wipe, wipeLoop, Code.allInstrs, GcmImpl.callees, noEsp_of vg.ctr.nosp,
    noEsp_of vg.ctr.expandNosp, noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem body_stackUse : stackUse (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg))) ≤ 32 := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush,
    ghCall, ghash1, j0, j0hash, lens, oneAad, oneEntry, oneTag, recv, tag, tagLenOk, openBody, decTo, wholeTo,
    ctrToCall, wipe, wipeLoop, stackUse, GcmImpl.callees, vg.ctr.stack, vg.ctr.expandStack,
    vg.gh.stack, Nat.max_le, X86.frameBytes, List.length_cons, List.length_nil, Nat.zero_le, true_and, and_true]
  decide +kernel

end

/-! ## Correct and constant time -/

/-- The public data of a run: the body's, and whether the tag is right. -/
abbrev idx (s : State) : OQ := ((pubTo s, arg s 8), (toRes s).isSome)

section
variable (vg : GcmImpl)

theorem openTo_eq : Open.openTo vg.callees (toFn vg) = .frame (.alloc 48)
    (.seq (.block frameArgs) (openBody vg.callees (toMode vg).bad (toMode vg).fail (toMode vg).dec)) (.free 48) :=
  rfl

theorem frameBody_noSp : NoSp (.seq (.block frameArgs)
    (openBody vg.callees (toMode vg).bad (toMode vg).fail (toMode vg).dec) : Prog isa) := by
  refine NoSp.of_all ?_
  show ((Code.block frameArgs : Prog isa).allInstrs _ && _) = true
  rw [show (toMode vg).dec = decTo vg.callees (toFn vg) from rfl, show (toMode vg).bad = wipe from rfl,
    show (toMode vg).fail = wipe from rfl, body_noEsp vg, Bool.and_true]
  decide

theorem openTo_pc (q : OQ) :
    Pc (fun (a : State) s => toPre s ∧ idx s = q ∧ s = a) (Open.openTo vg.callees (toFn vg))
      (fun a s' => abiPreserved a s' ∧ toX86.post a s') := by
  rw [openTo_eq]
  refine Pc.frameAlloc (by decide) (by decide) (by decide) (fun a s ⟨hs, _, _⟩ => by
    have := (TP.of hs).sp; omega_using [this]) (frameBody_noSp vg) ?_
  refine Pc.seq (Q := fun a e => toPre a ∧ idx a = q ∧ Entered a e) ?_ ?_
  · refine Pc.taint [.esp] (fun a s₁ ⟨s, ⟨hs, hq, hsa⟩, e₁⟩ => ?_) (fun a b s₁ s₂ ⟨x, ⟨_, hqx, _⟩, e₁⟩
        ⟨y, ⟨_, hqy, _⟩, e₂⟩ r hr => ?_) (by taint_decide)
    · subst e₁ hsa
      exact WP.mono (entered (TP.of hs)) fun e he => ⟨hs, hq, he⟩
    · simp only [List.mem_singleton] at hr; subst hr e₁ e₂
      rw [allocFrame_esp, allocFrame_esp]
      exact congrArg (fun (q : OQ) => q.1.1.1) (hqx.trans hqy.symm)
  obtain hsp : NoSp (openBody vg.callees (toMode vg).bad (toMode vg).fail (toMode vg).dec) :=
    NoSp.of_all (body_noEsp vg)
  refine Pc.mono (Pc.lift (Pc.frameSp (openBody_pc (toMode vg) q) hsp fun s₀ s ⟨hb, _, hs⟩ => by
      have := hb.op.sp
      have : stackUse (openBody vg.callees (toMode vg).bad (toMode vg).fail (toMode vg).dec) ≤ 32 :=
        body_stackUse vg
      rw [hs]; omega_arith)
      (fun _ e => e) fun a e ⟨ha, hq, he⟩ => ⟨he.bodyTo (TP.of ha), ?_, rfl⟩) (fun _ _ h => h)
    fun a s₂ ⟨e, ⟨ha, hq, he⟩, ⟨⟨abi, hx, hpost⟩, x, ⟨_, _, hxe⟩, hfr⟩, _, _⟩ mm u fl => ?_
  swap
  · rw [← hq, he.pub_eq, show (toMode vg).x e = dstOf e from rfl, he.dst_eq, he.res (TP.of ha)]
  subst hq
  rw [hxe] at hfr
  obtain T := TP.of ha
  have hP := T.hP
  obtain eE : w64 (a.gpr .esp) = w64 (Pf a) + BitVec.ofNat 64 48 := by
    rw [← aP hP (by decide)]; congr 1; exact (BitVec.sub_add_cancel _ _).symm
  obtain rF : (⟨w64 (a.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (Pf a), 48⟩ := by
    rw [eE]; exact (split_disj (by omega_using [])).symm
  obtain ret₁ : e.mem.readW (w64 (a.gpr .esp)) 32 = a.mem.readW (w64 (a.gpr .esp)) 32 :=
    he.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact rF) (by decide)
  obtain ret₂ : s₂.mem.readW (w64 (a.gpr .esp)) 32 = e.mem.readW (w64 (a.gpr .esp)) 32 := by
    refine hfr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rw [he.wr, T.wr] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rF
    · exact T.r_t
    · exact T.r_w
    · exact T.r_a
    · rw [he.esp]
      exact (ret_below (k := 80) T.sp).sub_right (region_sub_trans
        (below_sub (body_stackUse vg) (by rw [T.pN]; have := T.sp; omega_using [this])) T.stk_sub)
  -- The `free` loses the frame's bytes, which lie apart from the return
  -- address and the plaintext.
  obtain hs₂ : s₂.gpr .esp = Pf a := by rw [abi.1 _ (by decide), he.esp]
  rw [hs₂] at fl
  obtain ret₃ : mm.readW (w64 (a.gpr .esp)) 32 = s₂.mem.readW (w64 (a.gpr .esp)) 32 :=
    fl.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact rF) (by decide)
  obtain hdst : bytesAt mm ((arg a 8).setWidth 64) (arg a 7).toNat =
      bytesAt s₂.mem ((arg a 8).setWidth 64) (arg a 7).toNat :=
    Proof.AesGcm.bytesAt_congr fun i hi => fl.bytes (R := ⟨w64 (arg a 8), (arg a 7).toNat⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (T.k_t.sub_left (below_sub (by decide) T.sp)).symm)
      (show (arg a 7).toNat ≤ 2 ^ 64 by have := T.ft; omega_using [this]) hi
  refine ⟨⟨fun r hr => ?_, by
    show mm.readW _ 32 = _
    rw [ret₃, ret₂, ret₁]⟩, ?_⟩
  · show (freed 48 s₂).gpr r = a.gpr r
    simp only [calleeSaved, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [freed_gpr _ _ (by decide), abi.1 _ (by decide), he.gpr _ (by decide) (by decide)]
    · rw [freed_gpr _ _ (by decide), abi.1 _ (by decide), he.gpr _ (by decide) (by decide)]
    · rw [freed_gpr _ _ (by decide), abi.1 _ (by decide), he.gpr _ (by decide) (by decide)]
    · rw [freed_gpr _ _ (by decide), abi.1 _ (by decide), he.gpr _ (by decide) (by decide)]
    · rw [freed_esp, abi.1 _ (by decide), he.esp]; exact BitVec.sub_add_cancel _ _
  · have hres : oRes (idx a).1.1 e = toRes a := by rw [← openRes_eq hx.pub, he.res T]
    unfold PostO at hpost
    rw [hres] at hpost
    show (match toRes a with
      | some pt => ((freed 48 s₂).gpr .edx ++ (freed 48 s₂).gpr .eax).setWidth 32 = 1 ∧
          bytesAt mm ((arg a 8).setWidth 64) (arg a 7).toNat = pt
      | none => ((freed 48 s₂).gpr .edx ++ (freed 48 s₂).gpr .eax).setWidth 32 = 0 ∧
          bytesAt mm ((arg a 8).setWidth 64) (arg a 7).toNat = List.replicate (arg a 7).toNat 0)
    rw [hdst]
    simp only [ret32_eq, freed_gpr _ _ (show Reg.eax ≠ .esp by decide)]
    split
    · next pt hpt => rw [hpt] at hpost; exact hpost
    · next hpt => rw [hpt] at hpost; exact hpost

theorem openTo_correct (s : State) (hs : toX86.pre s) :
    ∃ t s', Exec isa (Open.openTo vg.callees (toFn vg)) s t s' ∧ abiPreserved s s' ∧ toX86.post s s' :=
  (openTo_pc vg (idx s)).wp s s ⟨hs, rfl, rfl⟩

theorem openTo_ct : ConstantTime isa toX86.pre toX86.pub (Open.openTo vg.callees (toFn vg)) := by
  refine Pc.constantTime idx (fun s₁ s₂ _ _ ⟨⟨hesp, ha⟩, hs⟩ => ?_) (openTo_pc vg) fun _ hs => ⟨hs, rfl, rfl⟩
  simp only [idx, pubTo, Pf, hesp, hs, ha 8 (by decide)]
  congr 3
  funext k
  split
  · rw [ha _ (by split <;> (try split) <;> omega_arith)]
  · rfl

end

/-! ## The contracts -/

/-- A state satisfying the precondition with the working space: no nonce,
additional data, text or tag; its thirteen argument slots at `0x8004`. -/
def toSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8015 then 0x21 else if a = 0x801d then 0x30 else if a = 0x8025 then 0x31
    else if a = 0x802d then 0x50 else if a = 0x8035 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3100, 0⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 52⟩]

section
variable (vg : GcmImpl)

/-- `open_to`'s public data include its leak, from which `pub` has whether
it succeeds (`rounds` being valid). -/
theorem openTo_verified : Verified X86.target (Open.openTo vg.callees (toFn vg)) toScratchK :=
  Verified.of_correct (openTo_correct vg) (openTo_ct vg)
    { pre := to_pre
      post := by sig_implies_post [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
        Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
        pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by
        intro s₁ s₂ h₁ h₂ h
        obtain hR₁ := (TP.of (to_pre s₁ h₁)).rounds
        obtain hR₂ := (TP.of (to_pre s₂ h₂)).rounds
        sig_pub [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
          pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
        sig_split h
        sig_reduce [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
          pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        sig_simp [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
          pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [Nat.forall_lt_succ_right,
          Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | (apply leak_bool hR₁ hR₂; with_reducible assumption)
      sat := by
        obtain a0 : arg toSat 0 = 0x1000 := by decide
        obtain a1 : arg toSat 1 = 10 := by decide
        obtain a2 : arg toSat 2 = 0x2000 := by decide
        obtain a3 : arg toSat 3 = 0 := by decide
        obtain a4 : arg toSat 4 = 0x2100 := by decide
        obtain a5 : arg toSat 5 = 0 := by decide
        obtain a6 : arg toSat 6 = 0x3000 := by decide
        obtain a7 : arg toSat 7 = 0 := by decide
        obtain a8 : arg toSat 8 = 0x3100 := by decide
        obtain a9 : arg toSat 9 = 0 := by decide
        obtain a10 : arg toSat 10 = 0x5000 := by decide
        obtain a11 : arg toSat 11 = 0 := by decide
        obtain a12 : arg toSat 12 = 0x4000 := by decide
        obtain e : argAddr toSat 0 = 0x8004 := by decide
        have esp : toSat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
          pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp] using toSat }

end

/-! ## In its frame

The frame of `withStackScratch` copies the arguments passed on the stack,
which needs the pre- and postconditions and the leak of `Spec.Gcm.openToSig`
to read the memory on entry only within the function's buffers: the key
context, the nonce, the additional data, `src` and the tag
(`openToPre_local`, `openToRoundsPost_local`, `openToLeak_local`, as
`Proof/AesGcm/ScratchOpenTo.lean` has them for `open_to_prepared`). -/

section
variable (pb : Nat)

theorem openToPre_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m₁ →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 11
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

/-- What `open_to` computes on the memory `m₂` is what it computes on `m₁`
where they agree on the buffers it reads. -/
theorem openToResult_local {m₁ m₂ : Mem} {ctx rd nonce nl aad al src len tag tl : BitVec 64}
    (hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14)
    (hc : ∀ i < 256, m₂ (ctx + BitVec.ofNat 64 i) = m₁ (ctx + BitVec.ofNat 64 i))
    (hn : ∀ i < nl.toNat, m₂ (nonce + BitVec.ofNat 64 i) = m₁ (nonce + BitVec.ofNat 64 i))
    (ha : ∀ i < al.toNat, m₂ (aad + BitVec.ofNat 64 i) = m₁ (aad + BitVec.ofNat 64 i))
    (hs : ∀ i < len.toNat, m₂ (src + BitVec.ofNat 64 i) = m₁ (src + BitVec.ofNat 64 i))
    (ht : ∀ i < tl.toNat, m₂ (tag + BitVec.ofNat 64 i) = m₁ (tag + BitVec.ofNat 64 i)) :
    openResult (ctxCiph m₂ ctx (rd.setWidth pb).toNat) (ctxH m₂ ctx) (tl.setWidth pb).toNat
        (bytesAt m₂ nonce (nl.setWidth pb).toNat) (bytesAt m₂ src (len.setWidth pb).toNat)
        (bytesAt m₂ aad (al.setWidth pb).toNat) (bytesAt m₂ tag (tl.setWidth pb).toNat) =
      openResult (ctxCiph m₁ ctx (rd.setWidth pb).toNat) (ctxH m₁ ctx) (tl.setWidth pb).toNat
        (bytesAt m₁ nonce (nl.setWidth pb).toNat) (bytesAt m₁ src (len.setWidth pb).toNat)
        (bytesAt m₁ aad (al.setWidth pb).toNat) (bytesAt m₁ tag (tl.setWidth pb).toNat) := by
  have := Nat.mod_le nl.toNat (2 ^ pb)
  have := Nat.mod_le al.toNat (2 ^ pb)
  have := Nat.mod_le len.toNat (2 ^ pb)
  have := Nat.mod_le tl.toNat (2 ^ pb)
  rw [ctxCiph_congr (le15 hr) hc, ctxH_congr hc,
    bytesAt_congr (p := nonce) (n := (nl.setWidth pb).toNat) fun i hi => hn i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith),
    bytesAt_congr (p := aad) (n := (al.setWidth pb).toNat) fun i hi => ha i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith),
    bytesAt_congr (p := src) (n := (len.setWidth pb).toNat) fun i hi => hs i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith),
    bytesAt_congr (p := tag) (n := (tl.setWidth pb).toNat) fun i hi => ht i (by
      rw [BitVec.toNat_setWidth] at hi; omega_using [this, hi])]

theorem openToRoundsPost_local : ∀ vs m₁ m₂ m' r, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m₁ m' r →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m₂ m' r
  dsimp only [Curry.apply, Proof.AesGcm.openToRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  rw [openToResult_local pb hr (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
    (agree_of hb.2.2.2.2.2)]
  exact h hr

/-- `Proof.AesGcm.openToRoundsPost` reads the memory on return only within the buffers. -/
theorem openToPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (Spec.Gcm.openToSig.words pb).length →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m m₁ r →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hpre hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tgl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.openToPre pb) _ m at hpre
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.Gcm.openToPre, ArgWord.ofRaw, IntTy.bits] at hpre
  dsimp only [Curry.apply, Proof.AesGcm.openToRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  have := Nat.mod_le dl.toNat (2 ^ pb)
  rw [Proof.AesGcm.bytesAt_congr (m₁ := m₁) (m₂ := m₂) (p := dst) (n := (len.setWidth pb).toNat) fun i hi =>
    agree_of hb.2.2.2.2.1 i (by
      rw [← hpre.2, BitVec.toNat_setWidth] at hi; omega_using [this, hi])]
  exact h hr

theorem openToLeak_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToLeak pb) vs m₁ =
      Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.openToLeak pb) _ m₁ =
    Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (Spec.Gcm.openToLeak pb) _ m₂
  dsimp only [Curry.apply, Spec.Gcm.openToLeak, ArgWord.ofRaw, IntTy.bits]
  by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14
  · simp only [hr, not_true_eq_false, ↓reduceIte]
    simp only [openToResult_local pb hr (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1)
      (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.2)]
    rfl
  · simp only [hr, not_false_eq_true, ↓reduceIte]

end

/-- A state satisfying `vg_aes_gcm_open_to`'s precondition, without the
working space: its twelve argument slots at `0x8004`. -/
def toFrameSat : State := { toSat with wr := [⟨0x3100, 0⟩, ⟨0x8004, 48⟩] }

theorem toFrameSat_pre : ∃ s, (Proof.AesGcm.openToRoundsContract X86.abi 2696).pre s := by
  implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [toFrameSat, toSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using toFrameSat

section
variable (vg : GcmImpl)

theorem openTo_noEsp : (Open.openTo vg.callees (toFn vg)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  show (!Taint.clobbers (.alloc 48) .esp && ((Code.block frameArgs : Prog isa).allInstrs _ &&
    (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg))).allInstrs _) && !Taint.clobbers (.free 48) .esp) = true
  rw [body_noEsp vg]
  decide

theorem openTo_stackUse : stackUse (Open.openTo vg.callees (toFn vg)) ≤ 80 := by
  have := body_stackUse vg
  show max 0 (stackUse (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg)))) + 48 ≤ 80
  omega_using [this]

/-- `open_to` in its frame of 2616 bytes, holding its working space. -/
theorem openTo_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2616 12 (Open.openTo vg.callees (toFn vg)))
      (Proof.AesGcm.openToRoundsContract X86.abi 2696) :=
  X86.Verified.stackScratch (sig := Spec.Gcm.openToSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openToPre X86.abi.ptrBits) (post := Proof.AesGcm.openToRoundsPost X86.abi.ptrBits)
    (wa := true) (stack := 80) (leak := some (Spec.Gcm.openToLeak X86.abi.ptrBits)) (bytes := 2616)
    (openTo_verified vg) (by decide) (openTo_noEsp vg) (openTo_stackUse vg) (openToPre_local _)
    (openToRoundsPost_local _) (openToPostOut_local _) toFrameSat_pre (hleak := openToLeak_local _)

theorem body_spSafe :
    (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg))).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush,
    ghCall, ghash1, j0, j0hash, lens, oneAad, oneEntry, oneTag, recv, tag, tagLenOk, openBody, decTo, wholeTo,
    ctrToCall, wipe, wipeLoop, Code.all, GcmImpl.callees, vg.ctr.spSafe, vg.ctr.expandSpSafe,
    vg.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

/-- No instruction writes `esp` but the frames' push and pop. -/
theorem openTo_spSafe :
    (Impl.StackScratch.X86.withStackScratch 2616 12 (Open.openTo vg.callees (toFn vg))).all
      (fun i => !X86.isa.writesSp i) = true := by
  refine withStackScratch_spSafe ?_
  show (!X86.isa.writesSp (.alloc 48) && ((Code.block frameArgs : Prog isa).all _ &&
    (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg))).all _) && !X86.isa.writesSp (.free 48)) = true
  rw [body_spSafe vg]
  decide

end

end VG.Proof.AesGcm.X86.OpenTo
