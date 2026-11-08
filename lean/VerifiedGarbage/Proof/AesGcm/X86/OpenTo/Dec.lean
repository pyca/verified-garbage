module

public import VerifiedGarbage.Proof.AesGcm.X86.Open
public import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.OneAad
import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
meta import VerifiedGarbage.Proof.AesGcm.X86.Open
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.X86
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State

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

theorem fit : 4 * ctrRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem n_lt : n < 2 ^ 32 := by have := h.fD; omega

theorem args : arg (pushed ctrRegs s).callEntry 0 = K ∧ arg (pushed ctrRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed ctrRegs s).callEntry 2 = C ∧ arg (pushed ctrRegs s).callEntry 3 = D ∧
    arg (pushed ctrRegs s).callEntry 4 = BitVec.ofNat 32 n ∧ arg (pushed ctrRegs s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit ctrRegs_esp (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.edi, h.ebp]

/-- The last argument: the word at the caller's `esp`, above the frame. -/
theorem arg6 : arg (pushed ctrRegs s).callEntry 6 = T := by
  have hn : 4 * ctrRegs.length ≤ (s.gpr .esp).toNat := by have := h.fit; omega
  have e : ((pushed ctrRegs s).gpr .esp).toNat = (s.gpr .esp).toNat - 24 := by
    rw [pushed_esp, sub_toNat hn]; rfl
  have hsp := h.fsp
  rw [arg_callEntry (by rw [e]; have := h.esp; omega) (by rw [e]; omega)]
  have ew : ((pushed ctrRegs s).gpr .esp + BitVec.ofNat 32 (4 * 6)).setWidth 64 = w64 (s.gpr .esp) := by
    rw [pushed_esp]; congr 1; rw [show (4 * ctrRegs.length : Nat) = 4 * 6 from rfl, BitVec.sub_add_cancel]
  rw [ew, (pushed_frame ctrRegs_esp hn).readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ret_below (k := 24) (by have := h.esp; omega)) (by decide)]
  exact h.dst

theorem sub24 : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 28) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below (s.gpr .esp) 28) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 28) (k := 24) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 28 = s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

/-- The callee's first six arguments, below `esp`. -/
theorem argsDisj {X : Region} (hb : (below (s.gpr .esp) 28).Disjoint X) : (toArgsR (s.gpr .esp)).Disjoint X := by
  refine hb.sub_left ?_
  have := below_inner (sp := s.gpr .esp) (a := 24) (b := 28) (k := 0) (by omega) h.esp
  simpa using this

theorem callPre : CallPre Proof.Aes.ctr32ToX86 ctrRegs (ctrToRd (s.gpr .esp) K D n) (ctrToWr C T S n) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have a6 := h.arg6
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat32 h.n_lt
  have eA : argAddr (pushed ctrRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed ctrRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 28 := by
    rw [callEntry_esp']; rfl
  have eL : argAddr (pushed ctrRegs s).callEntry 6 = w64 (s.gpr .esp) := by
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
    rw [sub_toNat (by have := h.esp; omega)]; have := h.fsp; omega
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
    WP isa (Open.ctrToCall ⟨v.ctr.calleeTo.name, v.ctr.calleeTo.code⟩) s (CtrToPost s K C D S T R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat32 h.n_lt
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  unfold Open.ctrToCall
  refine WP.callWith (rs := ctrRegs) (k := Proof.Aes.ctr32ToX86) v.ctr.okTo v.ctr.nospTo (by simp)
    ctrRegs_esp (by rw [v.ctr.toStack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := h.args
  have a6 := h.arg6
  rw [v.ctr.toStack] at f'
  have fE := callEntry_frame h.fit ctrRegs_esp
  rw [show 4 * ctrRegs.length + 4 = 28 from rfl] at fE
  obtain ⟨hdata, hctr⟩ := post
  simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, a6, hR, hn, m₂] at hdata hctr
  have eK := bytesAt_frame fE (p := w64 K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bk.sub_right (Region.sub_prefix hR')).symm) (by omega)
  rw [blockAt_frame fE (one_disj h.bc), blocksAt_frame fE (one_disj h.bd) (by have := h.fD; omega),
    eK] at hdata
  rw [blockAt_frame fE (one_disj h.bc)] at hctr
  refine ⟨rd', wr', cs', ?_, hdata, hctr⟩
  exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr

/-- Calls of `vg_aes_ctr32_to` with the same arguments and stack pointer in
both runs are constant time. -/
theorem ctrTo_ct (v : GcmImpl) {I : State → Prop} {K C D S T E : BitVec 32} {R n : Nat}
    (h : ∀ s, I s → CtrToCall s K C D S T R n ∧ s.gpr .esp = E) :
    CT I (Open.ctrToCall ⟨v.ctr.calleeTo.name, v.ctr.calleeTo.code⟩) := by
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
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
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
  k_t : (below p.1 28).Disjoint ⟨w64 T, (p.2 7).toNat⟩

/-- The precondition of `open`'s body out of place: `open`'s arguments, the
destination writable and apart, and the word at `esp`, which holds it, readable
(the last argument of `vg_aes_ctr32_to`). -/
structure BodyTo (s : State) : Prop where
  op : OP 11 10 s
  tg : Covers [⟨w64 (arg s 8), (arg s 9).toNat⟩] (s.rd ++ s.wr) ∧
    (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧
    (⟨w64 (arg s 8), (arg s 9).toNat⟩ : Region).Disjoint ⟨w64 (arg s 10), 2560⟩ ∧
    (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 8), (arg s 9).toNat⟩
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
  · simp only [auxO, rO] at h₂; exact D.w_t.sub_left (Lay.wSub (by omega))
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
      ⟨0, rfl, by omega, by rw [tg, h₁, add_zero32], by rw [tg, h₂, Nat.sub_zero], fun r _ _ => tg r, trd, twr,
        by rw [tm]; exact Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    rintro w v ⟨i, rfl, hi, edx, ecx, gv, rdv, wrv, fv, pv⟩
    have aD : w64 (D + BitVec.ofNat 32 i) = w64 D + BitVec.ofNat 64 i := w64_add (by omega)
    have hcn : (⟨w64 D, n⟩ : Region).Contains (w64 D + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    have win : InRegions v.wr (w64 (D + BitVec.ofNat 32 i)) 1 := by
      rw [wrv, aD]; exact hw _ _ ⟨_, List.mem_singleton_self _, hcn⟩
    obtain ⟨v', run', mem', edx', ecx', zf', g', rd', wr'⟩ :=
      zeroStep_ok v edx (by rw [gv _ (by decide) (by decide), h₀]) win
    refine WP.of_runBlock ⟨v', run', ?_⟩
    have f' : Frame [⟨w64 D, n⟩] u.mem v'.mem := by
      rw [mem', aD]; exact fv.writeW (List.mem_singleton_self _) _ hcn
    have p' : Proof.Zeroize.Prefix v'.mem (w64 D) (i + 1) := by
      rw [mem', aD]; exact Proof.Zeroize.prefix_writeW (w := 8) pv (by omega)
    have g'' : ∀ r, r ≠ .ecx → r ≠ .edx → v'.gpr r = u.gpr r := fun r a b => by rw [g' r a b, gv r a b]
    have hz : v'.zf = some (decide (i + 1 = n)) := by rw [zf', ecx, pred_beq hi hn]
    by_cases he : i + 1 = n
    · left
      exact ⟨by simp [eval, hz, he], by rw [← he]; exact p', f', g'', rd'.trans rdv, wr'.trans wrv⟩
    · right
      exact ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, edx',
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
  have lR := h.env.wIn' (d := lenO) (n := 4) (by decide)
  have lv := h.lenO
  rw [slotv_eq] at lv
  have hr' : InRegions (s.rd ++ s.wr) (w64 (s.gpr .esp + BitVec.ofNat 32 0)) 4 := by
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
  have gs : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r := fun r a b c => by
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
  have hcb : blockAt m cb = Nat.repeat inc32 (n / 16) icb := by rw [h.1]; congr 1; omega
  refine ⟨?_, ?_, fun h1 => absurd (by omega) h1⟩
  · refine list_ext (by simp [length_xorKs, length_bytesAt]) fun k hk => ?_
    simp only [length_bytesAt] at hk
    rw [getD_xorKs _ _ _ _ (by rw [length_bytesAt]; exact hk), getD_bytesAt' _ _ hk,
      getD_bytesAt' _ _ hk]
    have hq : k / 16 < nb := by omega
    have e₁ := congrArg (fun L => L.getD (k / 16) 0) hd
    rw [ctr32_getD _ _ _ (by rw [length_blocksAt]; exact hq), blocksAt_getD _ _ _ hq,
      blocksAt_getD _ _ _ hq] at e₁
    have ea : ∀ a : Addr, a + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (16 * (k / 16)) + BitVec.ofNat 64 (k % 16) :=
      fun a => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [ea dp, ea sp, bytes_toBytes_blockAt m' _ (by omega), bytes_toBytes_blockAt m _ (by omega), e₁,
      Proof.Aes.toBytes_xor _ _ (by omega), ksByte, hcb, ← repeat_add,
      show (n + k) / 16 = k / 16 + n / 16 by omega, show (n + k) % 16 = k % 16 by omega]
  · rw [hc, hcb, ← repeat_add]; congr 1; omega

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
  have hr := (p.2 7).isLt
  have hsh := shr4 hr
  refine ⟨_, by xrun [h.env.ebp, L.aW, h.env.wIn', hd, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hsh]
  · simp only [zf_setMem, gpr_setMem, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
      reduceCtorEq, hsh]
    rw [and_self_beq32 (by omega)]
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
  have := h.pre.op.fg; rw [pubSw_esp h.pub] at this; omega


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
  have hk : 16 * ((p.2 7).toNat / 16) ≤ (p.2 7).toNat := Nat.mul_div_le _ _
  have esp : s₁.gpr .esp = p.1 := by rw [g _ (by decide) (by decide) (by decide) (by decide), h.o.env.esp]
  have eS := L.aW (o := 512) (by decide)
  have cw := cb_w G
  have hsp := L.sp
  have hn := G.fd
  refine ⟨ax, cx, dx, by rw [g _ (by decide) (by decide) (by decide) (by decide), h.ebx],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.edi], bp, ?_, G.rounds, by rw [esp]; exact hsp,
    by rw [esp]; exact IX.fsp h.ix, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by have := L.fc; omega, ?_, by have := G.fd; omega, by have := D.fT; omega, ?_, ?_, ?_, ?_⟩
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
  · rw [esp]; exact L.kc.sub_right (Region.sub_prefix (by decide))
  · rw [esp]; exact L.kw.sub_right cw
  · rw [esp]; exact G.k_d.sub_right (Region.sub_prefix hk)
  · rw [esp]; exact D.k_t.sub_right (Region.sub_prefix hk)
  · rw [esp, eS]; exact L.kw.sub_right (Lay.wSub (by decide))
  · rw [esp]; exact G.r_w.sub_right cw
  · rw [esp]; exact D.r_t.sub_right (Region.sub_prefix hk)
  · rw [esp, eS]; exact G.r_w.sub_right (Lay.wSub (by decide))
  · rw [L.nS (by decide)]; have := L.fs; omega
  · rw [L.nW (by decide)]; have := L.fw; omega
  · rw [rd, wr, esp, h.o.rd, h.o.wr, ← pubSw_esp h.ix.pub]; exact h.ix.pre.last
  · rw [rd, wr]
    exact covers_cons (covers_pre h.o.env.ctxR (by decide) (by decide))
      (covers_cons (covers_pre h.o.dIn hk (by omega)) covers_nil)
  · rw [wr]
    refine covers_cons ?_ (covers_cons (covers_pre (by rw [h.o.wr]; exact IX.dW h.ix) hk (by omega))
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
  · exact ⟨below p.1 28, by simp, fun _ h => h⟩

omit D in
/-- A region apart from `W`, the whole blocks of the destination and the
stack, apart from what the call of `vg_aes_ctr32_to` writes. -/
theorem callFr_disj {X : Region} (hw : X.Disjoint ⟨w64 (p.2 8), 2560⟩)
    (ht : X.Disjoint ⟨w64 T, 16 * ((p.2 7).toNat / 16)⟩) (hk : (below p.1 28).Disjoint X) :
    ∀ r ∈ [(⟨w64 (stOf (p.2 8) + BitVec.ofNat 32 48), 16⟩ : Region), ⟨w64 T, 16 * ((p.2 7).toNat / 16)⟩,
      ⟨w64 (p.2 8 + BitVec.ofNat 32 512), 2048⟩, below p.1 28], X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (cb_w G)
  · exact ht
  · rw [G.L.aW (by decide)]; exact hw.sub_right (Lay.wSub (by decide))
  · exact hk.symm

theorem wholeCall_wp (vg : GcmImpl) {s₀ s : State} (h : W1 p T s₀ s) :
    WP isa (.seq (.block ctrArgs) (.seq (Open.ctrToCall ⟨vg.ctr.calleeTo.name, vg.ctr.calleeTo.code⟩)
      (.block unscr))) s (DW p T s₀) := by
  have L := G.L
  have hk : 16 * ((p.2 7).toNat / 16) ≤ (p.2 7).toNat := Nat.mul_div_le _ _
  obtain ⟨s₁, run, ax, cx, dx, bp, g, m, rd, wr⟩ := ctrArgs_ok L h.o.env h.o.rounds
  have hc := toCall G D h ax cx dx bp g m rd wr
  have esp₁ : s₁.gpr .esp = p.1 := by rw [g _ (by decide) (by decide) (by decide) (by decide), h.o.env.esp]
  refine WP.seq (WP.of_runBlock ⟨s₁, run, ?_⟩)
  refine WP.seq (WP.mono (ctrTo_call vg hc) fun s₂ g₂ => ?_)
  have bp₂ : s₂.gpr .ebp = p.2 8 + BitVec.ofNat 32 512 := by rw [g₂.saved .ebp (by decide), bp]
  refine WP.of_runBlock ⟨_, by xrun [unscr, bp₂], ?_⟩
  have f₂ := g₂.frame
  rw [esp₁, m] at f₂
  have hF : Frame (tF p T) s.mem s₂.mem := callFr_tF G f₂
  have out := g₂.out
  have ctr := g₂.ctr
  have hci : Spec.Gcm.aesWith (p.2 1).toNat (bytesAt s₁.mem (w64 (p.2 0)) (16 * ((p.2 1).toNat + 1))) = ciphP p s₀ := by
    rw [m]; exact h.o.ciph
  rw [hci, L.aS (by decide), m] at out
  rw [L.aS (by decide), m] at ctr
  have h0 : Ctr s.mem (w64 (stOf (p.2 8)) + BitVec.ofNat 64 48) (w64 (stOf (p.2 8)) + BitVec.ofNat 64 64)
      (ciphP p s₀) (icbP p s₀) 0 := Proof.Gcm.ctr_zero _ _ _ _ h.cb
  obtain ⟨wh, ct⟩ := ctr_whole_to h0 (by decide) out ctr
  have hsrc := congrArg (List.take (16 * ((p.2 7).toNat / 16))) h.data
  rw [bytesAt_take _ _ hk, bytesAt_take _ _ hk] at hsrc
  rw [hsrc] at wh
  rw [Nat.zero_add] at ct
  have esi : s₂.gpr .esi = s.gpr .esi := by
    rw [g₂.saved .esi (by decide), g _ (by decide) (by decide) (by decide) (by decide)]
  have esp : s₂.gpr .esp = s.gpr .esp := by
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
    · exact (L.stk_w (by decide)).symm
  · mems []
    rw [bytesAt_frame f₂ (callFr_disj G G.d_w (D.d_t.sub_right (Region.sub_prefix hk)) G.k_d)
      (by have := G.fd; omega)]
    exact h.data
  · mems []; exact wh
  · mems []; exact ct

theorem wholeCall_ct (vg : GcmImpl) :
    CT (fun s => ∃ s₀, W1 p T s₀ s) (.seq (.block ctrArgs)
      (.seq (Open.ctrToCall ⟨vg.ctr.calleeTo.name, vg.ctr.calleeTo.code⟩) (.block unscr))) := by
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
    Pc (OC BodyTo dstOf ((p, T), true)) (wholeTo ⟨vg.ctr.calleeTo.name, vg.ctr.calleeTo.code⟩) (DW p T) := by
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
  have hlt := (p.2 7).isLt
  have hand := and15 (BitVec.ofNat 32 (p.2 7).toNat)
  rw [toNat_ofNat32 hlt] at hand
  refine ⟨_, by xrun [tailLen, h.env.ebp, L.aW, h.env.wIn', hn], ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · regs [hand]
  · simp only [zf_setMem, gpr_setMem, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
      reduceCtorEq, hand]
    rw [and_self_beq32 (by omega)]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, ite_false]
  all_goals rfl

/-- The keystream block for the last bytes, after the whole blocks. -/
theorem ks_pc (vg : GcmImpl) (h0 : (p.2 7).toNat % 16 ≠ 0) :
    Pc (DW p T) (.seq (.block ksArgs) (.seq (ctrCall vg.callees) (.block unscr))) (KS p T) := by
  have L := G.L
  have hk : 16 * ((p.2 7).toNat / 16) ≤ (p.2 7).toNat := Nat.mul_div_le _ _
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
  have eC := L.aS (o := 48) (by decide)
  have eK := L.aS (o := 64) (by decide)
  have gf := g.frame
  rw [eC, eK] at gf
  have fz : Frame [⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 64, 16⟩] u.mem s₁.mem := by
    rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  -- What the two write, within `oF`.
  have sW : ∀ {d k : Nat}, d + k ≤ 80 → Region.Sub ⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 d, k⟩
      ⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩ := fun hdk => by
    rw [st_eq G]; exact Offset.sub _ (by omega) (by omega)
  have f : Frame (tF p T) u.mem s₂.mem := by
    refine Frame.trans (fz.sub fun r hr => ?_) (gf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sW (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, sW (by decide)⟩
      · exact ⟨_, by simp, sW (by decide)⟩
      · exact ⟨wsR (p.2 8), by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨below p.1 28, by simp, fun _ h => h⟩
  -- Through both writes, for a region apart from them.
  have two : ∀ {X : Region} {n : Nat}, n ≤ 2 ^ 64 → (∀ r ∈ [(⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 48, 16⟩ : Region),
      ⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 64, 16 * 1⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 512, 2048⟩, below p.1 28],
      X.Disjoint r) → X = ⟨X.base, n⟩ → bytesAt s₂.mem X.base n = bytesAt u.mem X.base n := by
    intro X n hn hX e
    have hz : ∀ r ∈ [(⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 64, 16⟩ : Region)], (⟨X.base, n⟩ : Region).Disjoint r :=
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← e]; exact hX _ (by simp)
    rw [bytesAt_frame gf (fun r hr => by rw [← e]; exact hX r hr) hn, bytesAt_frame fz hz hn]
  have ciph₁ : ciphOf s₁.mem (p.2 0) (p.2 1).toNat = ciphP p s₀ := by
    rw [ciph_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.cs.sub_right (by rw [stOf_w64 L.fw] at *; exact Lay.stSub (by decide))) G.rounds]
    exact h.o.ciph
  refine ⟨OEnv.frameT G D h.o f (by rw [g.env.ebp, h.o.env.ebp]) (by rw [g.env.esi, h.o.env.esi])
      (by rw [g.env.esp, h.o.env.esp]) (by rw [g.rd, rd₁]) (by rw [g.wr, wr₁]), h.ix, ?_, ?_, ?_, fun d hd => ?_⟩
  · have hX : ∀ r ∈ [(⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 48, 16⟩ : Region),
        ⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 64, 16 * 1⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 512, 2048⟩, below p.1 28],
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
        ⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 64, 16 * 1⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 512, 2048⟩, below p.1 28],
        (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact G.d_w.sub_right (region_sub_trans (sW (by decide)) (Lay.wSub (by decide)))
      · exact G.d_w.sub_right (region_sub_trans (sW (by decide)) (Lay.wSub (by decide)))
      · exact G.d_w.sub_right (Lay.wSub (by decide))
      · exact G.k_d.symm
    rw [two (X := ⟨w64 (p.2 6), (p.2 7).toNat⟩) (by have := G.fd; omega) hX rfl]; exact h.data
  · have tA : ∀ {A : Region}, A.Sub ⟨w64 (p.2 8), 2560⟩ →
        (⟨w64 T, 16 * ((p.2 7).toNat / 16)⟩ : Region).Disjoint A :=
      fun hA => (D.w_t.sub_left hA).symm.sub_left (Region.sub_prefix hk)
    rw [bytesAt_frame gf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact tA (region_sub_trans (sW (by decide)) (Lay.wSub (by decide)))
        · exact tA (region_sub_trans (sW (by decide)) (Lay.wSub (by decide)))
        · exact tA (Lay.wSub (by decide))
        · exact (D.k_t.sub_right (Region.sub_prefix hk)).symm) (by have := D.fT; omega),
      bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact tA (region_sub_trans (sW (by decide)) (Lay.wSub (by decide)))) (by have := D.fT; omega)]
    exact h.whole
  · rw [ciph₁] at hks
    have t := (Proof.Gcm.ctr_tail h.ctr (by omega) hks hcb (d := d) (by omega) (by omega)).1
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
  have hlt := (p.2 7).isLt
  have hand := and15 (BitVec.ofNat 32 (p.2 7).toNat)
  rw [toNat_ofNat32 hlt] at hand
  have h16 : BitVec.ofNat 32 (p.2 7).toNat - BitVec.ofNat 32 ((p.2 7).toNat % 16) =
      BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) hlt]; congr 1; omega
  have hr' : InRegions (s.rd ++ s.wr) (w64 (s.gpr .esp + BitVec.ofNat 32 0)) 4 := by
    rw [add_zero32, h.env.esp]; exact hr
  have hT' : s.mem.readW (w64 (s.gpr .esp + BitVec.ofNat 32 0)) 32 = T := by rw [add_zero32, h.env.esp]; exact hT
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
  rw [w64_add (by have := D.fT; omega)]; exact Offset.sub_base _ (by omega)

omit G in
/-- The first `16 k` bytes of the destination are apart from its last bytes. -/
theorem wh_tl : (⟨w64 T, 16 * ((p.2 7).toNat / 16)⟩ : Region).Disjoint
    ⟨w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))), (p.2 7).toNat % 16⟩ := by
  by_cases h0 : (p.2 7).toNat % 16 = 0
  · intro a _ h; simp only [Region.Contains] at h; omega
  rw [w64_add (by have := D.fT; omega)]; exact split_disj (by have := D.fT; omega)

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
  have hk : 16 * ((p.2 7).toNat / 16) ≤ (p.2 7).toNat := Nat.mul_div_le _ _
  have hfT := D.fT
  have hfd := G.fd
  refine Pc.taint [.edi, .edx, .ecx, .esi] (fun s₀ v ⟨u, h⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.edi, h₂.edi]
      · rw [h₁.edx, h₂.edx]
      · rw [h₁.ecx, h₂.ecx]
      · rw [h₁.esi, h₂.esi]) (by taint_decide)
  have eT : w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))) =
      w64 T + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16)) := w64_add (by omega)
  have eS : w64 (p.2 6 + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))) =
      w64 (p.2 6) + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16)) := w64_add (by omega)
  have eK := L.aS (o := 64) (by decide)
  have o := h.ks.o
  have dW : Covers [⟨w64 T, (p.2 7).toNat⟩] v.wr := by rw [h.wr, o.wr]; exact IX.dW h.ks.ix
  refine WP.mono (xorLoopG_ok true v ⟨h.edx, h.edi, h.esi, (fun e => nomatch e), h.ecx, by omega, by omega,
    by rw [L.nS (by decide)]; have := L.fs; omega, by rw [toNat_add32 (by omega)]; omega,
    by rw [toNat_add32 (by omega)]; omega, ?_, ?_, ?_, ?_, .inr ?_⟩) fun s' x => ⟨u, v, h, x⟩
  · rw [eK, h.rd, h.wr]; exact covers_left (o.env.stC (by omega))
  · rw [eS, h.rd, h.wr]; exact covers_off o.dIn (by omega) (by omega)
  · rw [eT]; exact covers_off dW (by omega) (by omega)
  · rw [eK, eT]
    exact ((D.w_t.sub_left (by rw [st_eq G]; exact Lay.wSub (by omega))).sub_right
      (Offset.sub_base _ (by omega)))
  · rw [eS, eT]
    exact (D.d_t.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))

/-- `esi` the state again, and the plaintext at the destination. -/
theorem fin_pc (h0 : (p.2 7).toNat % 16 ≠ 0) :
    Pc (fun s₀ s' => ∃ u v, XR p T s₀ u v ∧
      XorPostG true v (stOf (p.2 8) + BitVec.ofNat 32 64) (p.2 6 + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16)))
        (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))) ((p.2 7).toNat % 16) s')
      (.block [.mov .esi (.reg .ebp), .alu .add .esi (imm stO)]) (OD BodyTo dstOf outTo fbTo ((p, T), true)) := by
  have L := G.L
  have hk : 16 * ((p.2 7).toNat / 16) ≤ (p.2 7).toNat := Nat.mul_div_le _ _
  have hfT := D.fT
  refine Pc.taint [.ebp] (fun s₀ s ⟨u, v, h, x⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, x₁⟩ ⟨_, _, h₂, x₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [x₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebp,
        x₂.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₂.ebp,
        h₁.ks.o.env.ebp, h₂.ks.o.env.ebp]) (by taint_decide)
  have o := h.ks.o
  have bp : s.gpr .ebp = p.2 8 := by
    rw [x.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.ebp, o.env.ebp]
  have sp : s.gpr .esp = u.gpr .esp := by
    rw [x.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.esp]
  refine WP.of_runBlock ⟨_, by xrun [bp], ?_⟩
  have eT : w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))) =
      w64 T + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16)) := w64_add (by omega)
  have hxl := length_xorBytes u.mem (w64 (p.2 6 + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))))
    (w64 (stOf (p.2 8) + BitVec.ofNat 32 64)) ((p.2 7).toNat % 16)
  have fw : Frame [⟨w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))), (p.2 7).toNat % 16⟩] u.mem s.mem := by
    rw [x.mem, h.mem]; exact writeBytes_frame' _ hxl
  have tl : ∀ {X : Region}, X.Disjoint ⟨w64 T, (p.2 7).toNat⟩ →
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
    have spl : ∀ (m : Mem) (a : Addr), bytesAt m a (p.2 7).toNat =
        bytesAt m a (16 * ((p.2 7).toNat / 16)) ++
          bytesAt m (a + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16))) ((p.2 7).toNat % 16) := fun m a => by
      rw [← bytesAt_add]; congr 1; omega
    have hw : bytesAt s.mem (w64 T) (16 * ((p.2 7).toNat / 16)) = bytesAt u.mem (w64 T) (16 * ((p.2 7).toNat / 16)) :=
      bytesAt_frame fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact wh_tl D) (by omega)
    have ws := bytesAt_writeBytes_self u.mem (w64 (T + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))))
      (xorBytes u.mem (w64 (p.2 6 + BitVec.ofNat 32 (16 * ((p.2 7).toNat / 16))))
        (w64 (stOf (p.2 8) + BitVec.ofNat 32 64)) ((p.2 7).toNat % 16)) (by rw [hxl]; omega)
    rw [hxl] at ws
    have src := congrArg (List.drop (16 * ((p.2 7).toNat / 16))) h.ks.data
    rw [bytesAt_drop _ _ hk, bytesAt_drop _ _ hk, show (p.2 7).toNat - 16 * ((p.2 7).toNat / 16) =
      (p.2 7).toNat % 16 by omega] at src
    have kb := h.ks.kb (bytesAt u.mem (w64 (p.2 6) + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16)))
      ((p.2 7).toNat % 16)) (length_bytesAt _ _ _)
    rw [src] at kb
    have tailEq : bytesAt s.mem (w64 T + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16))) ((p.2 7).toNat % 16) =
        xorKs (ciphP p s₀) (icbP p s₀) (16 * ((p.2 7).toNat / 16))
          (bytesAt s₀.mem (w64 (p.2 6) + BitVec.ofNat 64 (16 * ((p.2 7).toNat / 16))) ((p.2 7).toNat % 16)) := by
      rw [← eT, x.mem, h.mem, ws, xorBytes, w64_add (show (p.2 6).toNat + 16 * ((p.2 7).toNat / 16) < 2 ^ 32 by
        have := G.fd; omega), L.aS (o := 64) (by decide), src]
      exact kb
    rw [spl, spl, Proof.Gcm.gctr_eq, Proof.Gcm.xorKs_append, length_bytesAt, Nat.zero_add, hw, h.ks.whole, tailEq]

end

/-- `decTo`: the data decrypted to the destination. -/
theorem decTo_pc (vg : GcmImpl) (q : OQ) (ht : q.2 = true) :
    Pc (OC BodyTo dstOf q) (decTo vg.callees ⟨vg.ctr.calleeTo.name, vg.ctr.calleeTo.code⟩)
      (OD BodyTo dstOf outTo fbTo q) := by
  obtain ⟨⟨p, T⟩, b⟩ := q
  dsimp only at ht
  subst ht
  by_cases hex : ∃ s₀ s, OC BodyTo dstOf ((p, T), true) s₀ s
  swap
  · exact Pc.vacuous fun a s h => hex ⟨a, s, h⟩
  obtain ⟨z, w, hz⟩ := hex
  have G : OL p := hz.ix.pre.op.ol rfl (by decide) hz.ix.pub
  have D : DL p T := IX.dl hz.ix
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
    rw [show 16 * ((p.2 7).toNat / 16) = (p.2 7).toNat by omega] at hw
    rw [Proof.Gcm.gctr_eq]; exact hw
  · have h0 : (p.2 7).toNat % 16 ≠ 0 := by simpa using hb
    exact Pc.seq (Pc.mono (ks_pc G D vg h0) (fun _ _ h => h.1) fun _ _ h => h)
      (Pc.seq (regs_pc G) (Pc.seq (xor_pc G D h0) (fin_pc G D h0)))

end VG.Proof.AesGcm.X86.OpenTo
