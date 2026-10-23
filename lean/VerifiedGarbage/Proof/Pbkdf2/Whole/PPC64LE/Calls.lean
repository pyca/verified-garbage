module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Finalize
import VerifiedGarbage.Proof.Pbkdf2.Stream.PPC64LE.Iterate
import VerifiedGarbage.Proof.Framework.Contract

/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: the calls

The calls of HMAC's `init` (against its shared contract, `WP.callAny`, since
it allocates its working space on the stack), of HMAC's `finalize` and of
`iterate` (against the contracts of their generic proofs, `WP.callF`): what
each needs of the state it is called from, and what holds when it returns.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK finG)
open VG.Proof.Pbkdf2.Stream.PPC64LE (iterG)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns} (hF : FnsOK F)

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers, and memory outside `ws`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame ws s.mem s'.mem

/-! ## HMAC's `init` -/

/-- What a call of HMAC's `init` needs of the state it is called from: the
key's `kl` bytes at `k` and the states at `inn` and `ou`. -/
structure HiArgs (hF : FnsOK F) (s : State) (inn ou k : Addr) (kl : Nat) : Prop where
  h3 : s.gpr .r3 = inn
  h4 : s.gpr .r4 = ou
  h5 : s.gpr .r5 = k
  h6 : (s.gpr .r6).toNat = kl
  sp : hF.X + 96 ≤ s.sp.toNat
  d_io : Region.Disjoint ⟨inn, F.H.S⟩ ⟨ou, F.H.S⟩
  d_ik : Region.Disjoint ⟨inn, F.H.S⟩ ⟨k, kl⟩
  d_ok : Region.Disjoint ⟨ou, F.H.S⟩ ⟨k, kl⟩
  b_i : (below s.sp (hF.X + 96)).Disjoint ⟨inn, F.H.S⟩
  b_o : (below s.sp (hF.X + 96)).Disjoint ⟨ou, F.H.S⟩
  b_k : (below s.sp (hF.X + 96)).Disjoint ⟨k, kl⟩
  n_i : inn.toNat + F.H.S ≤ 2 ^ 64
  n_o : ou.toNat + F.H.S ≤ 2 ^ 64
  n_k : k.toNat + kl ≤ 2 ^ 64
  hc : Covers ([⟨k, kl⟩] ++ [⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩]) (s.rd ++ s.wr)
  hw : Covers [⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩] s.wr

theorem HiArgs.pre {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs hF s inn ou k kl) :
    (hiK hF.hH.SH hF.X).pre (s.callEntry.withRegions [⟨k, kl⟩]
      [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]) := by
  have hS := hF.hH.hS
  sig_pre [Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, PPC64LE.abi, PPC64LE.argRegs]
  rw [show hF.X + 95 + 1 = hF.X + 96 from rfl]
  simp only [h.h3, h.h4, h.h5, h.h6, hS]
  exact ⟨h.sp, trivial, trivial, h.d_io, h.d_ik, h.d_ok, h.b_i, h.b_o, h.b_k, h.n_i, h.n_o, h.n_k⟩

/-- HMAC's `init` with the key's `kl` bytes at `k`, into the states at `inn` and `ou`. -/
theorem hi_call {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs hF s inn ou k kl) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩] ++ [below s.sp (hF.X + 96)]) s' →
      hF.hH.SH.Repr s'.mem inn (xorPad (blockKey hF.hH.SH.H (bytesAt s.mem k kl)) ipad) →
      hF.hH.SH.Repr s'.mem ou (xorPad (blockKey hF.hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa F.callHi s Q := by
  have hS := hF.hH.hS
  refine WP.callAny (k := hiK hF.hH.SH hF.X) hF.hi (rd := [⟨k, kl⟩])
    (wr := [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]) h.pre (by rw [hS]; exact h.hc)
    (by rw [hS]; exact h.hw) ?_ (by have := hF.hiSd; have := hF.hX; omega)
  intro s' hrd hwr hsp' hf hcs hpost
  sig_post [Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.initPost, PPC64LE.abi,
    PPC64LE.argRegs] at hpost
  simp only [h.h3, h.h4, h.h5, h.h6] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost.1 hpost.2
  rw [hS] at hf
  exact Frame.below_mono hf hF.hiSd (by have := hF.hX; omega)

/-- Two runs of a call of HMAC's `init` with the same arguments. -/
theorem hi_rel {P : State → State → Prop} {inn ou k : Addr} {kl : Nat}
    (h : ∀ s s', P s s' → HiArgs hF s inn ou k kl ∧ HiArgs hF s' inn ou k kl ∧ s.sp = s'.sp) :
    RelCT isa P F.callHi fun _ _ => True := by
  have hS := hF.hH.hS
  refine RelCT.call hF.hi hF.hiCt [⟨k, kl⟩] [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]
    fun s s' hp => ?_
  obtain ⟨a, a', e⟩ := h s s' hp
  refine ⟨a.pre, a'.pre, ?_, by rw [hS]; exact a.hc, by rw [hS]; exact a.hw, by rw [hS]; exact a'.hc,
    by rw [hS]; exact a'.hw⟩
  sig_pub [Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨e, a.h3.trans a'.h3.symm, a.h4.trans a'.h4.symm, a.h5.trans a'.h5.symm,
    BitVec.eq_of_toNat_eq (a.h6.trans a'.h6.symm)⟩

/-! ## HMAC's `finalize` -/

/-- What a call of HMAC's `finalize` needs: the inner state at `inn`, the
outer state at `ou`, `out` at `o` and the working space at `sc`. -/
structure HfArgs (F : Fns) (s : State) (inn ou o sc : Addr) : Prop where
  h3 : s.gpr .r3 = inn
  h4 : s.gpr .r4 = ou
  h6 : s.gpr .r6 = o
  h7 : s.gpr .r7 = sc
  sp : 96 ≤ s.sp.toNat
  d_iu : Region.Disjoint ⟨inn, F.H.S⟩ ⟨ou, F.H.S⟩
  d_io : Region.Disjoint ⟨inn, F.H.S⟩ ⟨o, F.H.D⟩
  d_is : Region.Disjoint ⟨inn, F.H.S⟩ ⟨sc, F.H.W + 48 + F.H.FD⟩
  d_uo : Region.Disjoint ⟨ou, F.H.S⟩ ⟨o, F.H.D⟩
  d_us : Region.Disjoint ⟨ou, F.H.S⟩ ⟨sc, F.H.W + 48 + F.H.FD⟩
  d_os : Region.Disjoint ⟨o, F.H.D⟩ ⟨sc, F.H.W + 48 + F.H.FD⟩
  b_i : (below s.sp 96).Disjoint ⟨inn, F.H.S⟩
  b_u : (below s.sp 96).Disjoint ⟨ou, F.H.S⟩
  b_o : (below s.sp 96).Disjoint ⟨o, F.H.D⟩
  b_s : (below s.sp 96).Disjoint ⟨sc, F.H.W + 48 + F.H.FD⟩
  hc : Covers ([⟨ou, F.H.S⟩] ++ [⟨inn, F.H.S⟩, ⟨o, F.H.D⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩]) (s.rd ++ s.wr)
  hw : Covers [⟨inn, F.H.S⟩, ⟨o, F.H.D⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩] s.wr

theorem HfArgs.pre {s : State} {inn ou o sc : Addr} (h : HfArgs F s inn ou o sc) :
    (finG hF.hH.SH (F.H.W + 48 + F.H.FD) 96).pre (s.callEntry.withRegions [⟨ou, hF.hH.SH.stateBytes⟩]
      [⟨inn, hF.hH.SH.stateBytes⟩, ⟨o, hF.hH.SH.digestBytes⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩]) := by
  have hS := hF.hH.hS; have hD := hF.hH.hD
  simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r7 ∉ linkRegs), h.h3, h.h4, h.h6, h.h7, hS, hD]
  exact ⟨trivial, trivial, h.d_iu, h.d_io, h.d_is, h.d_uo, h.d_us, h.d_os, h.sp, h.b_i, h.b_u, h.b_o, h.b_s⟩

theorem fin_ok : ∀ s, (finG hF.hH.SH (F.H.W + 48 + F.H.FD) 96).pre s → ∃ t s', Exec isa F.H.finalize s t s' ∧
    abiPreserved s s' ∧ (finG hF.hH.SH (F.H.W + 48 + F.H.FD) 96).post s s' := fun s hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.PPC64LE.Finalize.correct hF.hH hs
  exact ⟨t, s', he, h₁, h₂⟩

/-- HMAC's `finalize` of the inner state at `inn` and the outer state at
`ou`, with `count` in `r5`, into `o`, with the working space at `sc`. -/
theorem hf_call {s : State} {inn ou o sc : Addr} (h : HfArgs F s inn ou o sc) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, F.H.S⟩, ⟨o, F.H.D⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩] ++ [below s.sp 96]) s' →
      (∀ k0 text, k0.length = F.H.B → k0.length + text.length < 2 ^ 64 →
        hF.hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) →
        s.gpr .r5 = BitVec.ofNat 64 (F.H.B + text.length) →
        hF.hH.SH.Repr s.mem ou (xorPad k0 opad) →
        bytesAt s'.mem o F.H.D = hmacBlockKey hF.hH.SH.H k0 text) → Q s') :
    WP isa F.callHf s Q := by
  have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have hfd : F.H.finalize.fdepth ≤ 2 := by
    have := VG.Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_fdepth hF.hH
    simp only [Hash.finalize, Code.fdepth]; omega
  have hpf : pushFrames F.H.finalize = true := by
    simp [Hash.finalize, pushFrames, Instr.isPush, VG.Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_pf hF.hH]
  have c3 : s.callEntry.gpr .r3 = inn := (State.callEntry_gpr _ (by decide)).trans h.h3
  have c4 : s.callEntry.gpr .r4 = ou := (State.callEntry_gpr _ (by decide)).trans h.h4
  have c5 : s.callEntry.gpr .r5 = s.gpr .r5 := State.callEntry_gpr _ (by decide)
  have c6 : s.callEntry.gpr .r6 = o := (State.callEntry_gpr _ (by decide)).trans h.h6
  refine WP.callF (k := finG hF.hH.SH (F.H.W + 48 + F.H.FD) 96) (fin_ok hF) (h.pre hF)
    (by rw [hS, hD]; exact h.hc) (by rw [hS, hD]; exact h.hw) ?_ (by omega) hpf
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6,
    hD, hB] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
  rw [hS, hD] at hf
  exact Frame.below_mono hf (by omega) (by omega)

include hF in
/-- Two runs of a call of HMAC's `finalize` with the same arguments. -/
theorem hf_rel {P : State → State → Prop} {inn ou o sc : Addr}
    (h : ∀ s s', P s s' → HfArgs F s inn ou o sc ∧ HfArgs F s' inn ou o sc ∧ s.sp = s'.sp ∧
      s.gpr .r5 = s'.gpr .r5) :
    RelCT isa P F.callHf fun _ _ => True := by
  have hS := hF.hH.hS; have hD := hF.hH.hD
  refine RelCT.call (fin_ok hF) hF.hfCt [⟨ou, hF.hH.SH.stateBytes⟩]
    [⟨inn, hF.hH.SH.stateBytes⟩, ⟨o, hF.hH.SH.digestBytes⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e5⟩ := h s s' hp
  refine ⟨a.pre hF, a'.pre hF, ?_, by rw [hS, hD]; exact a.hc, by rw [hS, hD]; exact a.hw,
    by rw [hS, hD]; exact a'.hc, by rw [hS, hD]; exact a'.hw⟩
  simp only [finG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r4 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r5 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r6 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r7 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r7 ∉ linkRegs),
    a.h3, a'.h3, a.h4, a'.h4, a.h6, a'.h6, a.h7, a'.h7, e5]
  rw [e]; simp

/-! ## `iterate` -/

/-- What a call of `iterate` needs: the key's states at `key`, `U` at `u`,
`T` at `t` and the working space at `sc`. -/
structure ItArgs (F : Fns) (s : State) (key u t sc : Addr) : Prop where
  h3 : s.gpr .r3 = key
  h4 : s.gpr .r4 = u
  h6 : s.gpr .r6 = t
  h7 : s.gpr .r7 = sc
  sp : 96 ≤ s.sp.toNat
  d_kt : Region.Disjoint ⟨key, 2 * F.H.S⟩ ⟨t, F.H.D⟩
  d_ks : Region.Disjoint ⟨key, 2 * F.H.S⟩ ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩
  d_ut : Region.Disjoint ⟨u, F.H.D⟩ ⟨t, F.H.D⟩
  d_us : Region.Disjoint ⟨u, F.H.D⟩ ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩
  d_ts : Region.Disjoint ⟨t, F.H.D⟩ ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩
  b_k : (below s.sp 96).Disjoint ⟨key, 2 * F.H.S⟩
  b_u : (below s.sp 96).Disjoint ⟨u, F.H.D⟩
  b_t : (below s.sp 96).Disjoint ⟨t, F.H.D⟩
  b_s : (below s.sp 96).Disjoint ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩
  hc : Covers ([⟨key, 2 * F.H.S⟩, ⟨u, F.H.D⟩] ++ [⟨t, F.H.D⟩, ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩])
    (s.rd ++ s.wr)
  hw : Covers [⟨t, F.H.D⟩, ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩] s.wr

theorem ItArgs.pre {s : State} {key u t sc : Addr} (h : ItArgs F s key u t sc) :
    (iterG hF.hH.SH (Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H) 96).pre (s.callEntry.withRegions
      [⟨key, 2 * hF.hH.SH.stateBytes⟩, ⟨u, hF.hH.SH.digestBytes⟩]
      [⟨t, hF.hH.SH.digestBytes⟩, ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩]) := by
  have hS := hF.hH.hS; have hD := hF.hH.hD
  simp only [iterG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r7 ∉ linkRegs), h.h3, h.h4, h.h6, h.h7, hS, hD]
  exact ⟨trivial, trivial, h.d_kt, h.d_ks, h.d_ut, h.d_us, h.d_ts, h.sp, h.b_k, h.b_u, h.b_t, h.b_s⟩

theorem it_ok : ∀ s, (iterG hF.hH.SH (Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H) 96).pre s → ∃ t s',
    Exec isa (Impl.Pbkdf2.Stream.PPC64LE.iterate F.H) s t s' ∧ abiPreserved s s' ∧
      (iterG hF.hH.SH (Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H) 96).post s s' := fun s hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Pbkdf2.Stream.PPC64LE.Iter.correct hF.hH hs
  exact ⟨t, s', he, h₁, h₂⟩

/-- `iterate` with the key's states at `key`, `U` at `u`, `n` in `r5`, `T` at
`t` and the working space at `sc`. -/
theorem it_call {s : State} {key u t sc : Addr} (h : ItArgs F s key u t sc) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨t, F.H.D⟩, ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩] ++ [below s.sp 96]) s' →
      (∀ k0, k0.length = F.H.B → hF.hH.SH.Repr s.mem key (xorPad k0 ipad) →
        hF.hH.SH.Repr s.mem (key + BitVec.ofNat 64 F.H.S) (xorPad k0 opad) →
        bytesAt s'.mem t F.H.D = Spec.Pbkdf2.iterate (hmacBlockKey hF.hH.SH.H k0)
          ((s.gpr .r5).setWidth 32).toNat (bytesAt s.mem u F.H.D) (bytesAt s.mem t F.H.D)) → Q s') :
    WP isa F.callIt s Q := by
  have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have hfd : (Impl.Pbkdf2.Stream.PPC64LE.iterate F.H).fdepth ≤ 2 := by
    have := VG.Proof.Pbkdf2.Stream.PPC64LE.Iter.iterateMain_fdepth hF.hH
    simp only [Impl.Pbkdf2.Stream.PPC64LE.iterate, Impl.Pbkdf2.Stream.PPC64LE.iterateBody, Code.fdepth]; omega
  have hpf : pushFrames (Impl.Pbkdf2.Stream.PPC64LE.iterate F.H) = true := by
    simp [Impl.Pbkdf2.Stream.PPC64LE.iterate, Impl.Pbkdf2.Stream.PPC64LE.iterateBody, pushFrames, Instr.isPush,
      VG.Proof.Pbkdf2.Stream.PPC64LE.Iter.iterateMain_pf hF.hH]
  have c3 : s.callEntry.gpr .r3 = key := (State.callEntry_gpr _ (by decide)).trans h.h3
  have c4 : s.callEntry.gpr .r4 = u := (State.callEntry_gpr _ (by decide)).trans h.h4
  have c5 : s.callEntry.gpr .r5 = s.gpr .r5 := State.callEntry_gpr _ (by decide)
  have c6 : s.callEntry.gpr .r6 = t := (State.callEntry_gpr _ (by decide)).trans h.h6
  refine WP.callF (k := iterG hF.hH.SH (Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H) 96) (it_ok hF) (h.pre hF)
    (by rw [hS, hD]; exact h.hc) (by rw [hD]; exact h.hw) ?_ (by omega) hpf
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [iterG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6,
    hD, hB, hS] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
  rw [hD] at hf
  exact Frame.below_mono hf (by omega) (by omega)

include hF in
/-- Two runs of a call of `iterate` with the same arguments. -/
theorem it_rel {P : State → State → Prop} {key u t sc : Addr}
    (h : ∀ s s', P s s' → ItArgs F s key u t sc ∧ ItArgs F s' key u t sc ∧ s.sp = s'.sp ∧
      (s.gpr .r5).setWidth 32 = (s'.gpr .r5).setWidth 32) :
    RelCT isa P F.callIt fun _ _ => True := by
  have hS := hF.hH.hS; have hD := hF.hH.hD
  refine RelCT.call (it_ok hF) hF.itCt [⟨key, 2 * hF.hH.SH.stateBytes⟩, ⟨u, hF.hH.SH.digestBytes⟩]
    [⟨t, hF.hH.SH.digestBytes⟩, ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e5⟩ := h s s' hp
  refine ⟨a.pre hF, a'.pre hF, ?_, by rw [hS, hD]; exact a.hc, by rw [hD]; exact a.hw,
    by rw [hS, hD]; exact a'.hc, by rw [hD]; exact a'.hw⟩
  simp only [iterG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r4 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r5 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r6 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r7 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r7 ∉ linkRegs),
    a.h3, a'.h3, a.h4, a'.h4, a.h6, a'.h6, a.h7, a'.h7, e5]
  rw [e]; simp

/-! ## The streaming `update` -/

/-- What a call of the streaming `update` needs: the state at `st`, the
`len` bytes at `dat` and the working space at `sc`. -/
structure UpdArgs (F : Fns) (s : State) (st dat sc : Addr) (len : Nat) : Prop where
  h3 : s.gpr .r3 = st
  h5 : s.gpr .r5 = dat
  h6 : (s.gpr .r6).toNat = len
  h7 : s.gpr .r7 = sc
  d₁ : Region.Disjoint ⟨st, F.H.S⟩ ⟨sc, F.H.W⟩
  d₂ : Region.Disjoint ⟨dat, len⟩ ⟨st, F.H.S⟩
  d₃ : Region.Disjoint ⟨dat, len⟩ ⟨sc, F.H.W⟩
  sp : 48 ≤ s.sp.toNat
  s₁ : (below s.sp 48).Disjoint ⟨st, F.H.S⟩
  s₂ : (below s.sp 48).Disjoint ⟨dat, len⟩
  s₃ : (below s.sp 48).Disjoint ⟨sc, F.H.W⟩
  hc : Covers ([⟨dat, len⟩] ++ [⟨st, F.H.S⟩, ⟨sc, F.H.W⟩]) (s.rd ++ s.wr)
  hw : Covers [⟨st, F.H.S⟩, ⟨sc, F.H.W⟩] s.wr

/-- The streaming `update`, as `HashOK.callUpd_ok` gives it. -/
theorem upd_call (hH : HashOK F.H) {s : State} {st dat sc : Addr} {len : Nat} (h : UpdArgs F s st dat sc len)
    {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨st, F.H.S⟩, ⟨sc, F.H.W⟩] ++ [below s.sp 48]) s' →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .r4 = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem dat len)) → Q s') :
    WP isa F.H.callUpd s Q :=
  hH.callUpd_ok h.h3 h.h5 h.h6 h.h7 h.d₁ h.d₂ h.d₃ h.sp h.s₁ h.s₂ h.s₃ h.hc h.hw
    fun s' a b c d e f => hQ s' ⟨a, b, c, e, d⟩ f

end VG.Proof.Pbkdf2.Whole.PPC64LE
