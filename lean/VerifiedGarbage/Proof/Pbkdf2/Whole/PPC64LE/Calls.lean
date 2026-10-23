module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Common
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

include hF in
/-- HMAC's `init` with the key's `kl` bytes at `k`, into the states at `inn` and `ou`. -/
theorem hi_call {s : State} {inn ou k : Addr} {kl : Nat}
    (h3 : s.gpr .r3 = inn) (h4 : s.gpr .r4 = ou) (h5 : s.gpr .r5 = k) (h6 : (s.gpr .r6).toNat = kl)
    (hsp : hF.X + 96 ≤ s.sp.toNat)
    (d_io : Region.Disjoint ⟨inn, F.H.S⟩ ⟨ou, F.H.S⟩) (d_ik : Region.Disjoint ⟨inn, F.H.S⟩ ⟨k, kl⟩)
    (d_ok : Region.Disjoint ⟨ou, F.H.S⟩ ⟨k, kl⟩)
    (b_i : (below s.sp (hF.X + 96)).Disjoint ⟨inn, F.H.S⟩) (b_o : (below s.sp (hF.X + 96)).Disjoint ⟨ou, F.H.S⟩)
    (b_k : (below s.sp (hF.X + 96)).Disjoint ⟨k, kl⟩)
    (n_i : inn.toNat + F.H.S ≤ 2 ^ 64) (n_o : ou.toNat + F.H.S ≤ 2 ^ 64) (n_k : k.toNat + kl ≤ 2 ^ 64)
    (hc : Covers ([⟨k, kl⟩] ++ [⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩] ++ [below s.sp (hF.X + 96)]) s' →
      hF.hH.SH.Repr s'.mem inn (xorPad (blockKey hF.hH.SH.H (bytesAt s.mem k kl)) ipad) →
      hF.hH.SH.Repr s'.mem ou (xorPad (blockKey hF.hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa F.callHi s Q := by
  have hS := hF.hH.hS
  refine WP.callAny (k := hiK hF.hH.SH hF.X) hF.hi (rd := [⟨k, kl⟩])
    (wr := [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]) ?_ (by rw [hS]; exact hc)
    (by rw [hS]; exact hw) ?_ (by have := hF.hiSd; have := hF.hX; omega)
  · sig_pre [Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, PPC64LE.abi, PPC64LE.argRegs]
    rw [show hF.X + 95 + 1 = hF.X + 96 from rfl]
    simp only [h3, h4, h5, h6, hS]
    exact ⟨hsp, trivial, trivial, d_io, d_ik, d_ok, b_i, b_o, b_k, n_i, n_o, n_k⟩
  · intro s' hrd hwr hsp' hf hcs hpost
    sig_post [Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.initPost, PPC64LE.abi,
      PPC64LE.argRegs] at hpost
    simp only [h3, h4, h5, h6] at hpost
    refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost.1 hpost.2
    rw [hS] at hf
    exact Frame.below_mono hf hF.hiSd (by have := hF.hX; omega)

include hF in
/-- HMAC's `finalize` of the inner state at `inn` and the outer state at
`ou`, with `count` in `r5`, into `o`, with the working space at `sc`. -/
theorem hf_call {s : State} {inn ou o sc : Addr}
    (h3 : s.gpr .r3 = inn) (h4 : s.gpr .r4 = ou) (h6 : s.gpr .r6 = o) (h7 : s.gpr .r7 = sc)
    (hsp : 96 ≤ s.sp.toNat)
    (d_iu : Region.Disjoint ⟨inn, F.H.S⟩ ⟨ou, F.H.S⟩) (d_io : Region.Disjoint ⟨inn, F.H.S⟩ ⟨o, F.H.D⟩)
    (d_is : Region.Disjoint ⟨inn, F.H.S⟩ ⟨sc, F.H.W + 48 + F.H.FD⟩)
    (d_uo : Region.Disjoint ⟨ou, F.H.S⟩ ⟨o, F.H.D⟩) (d_us : Region.Disjoint ⟨ou, F.H.S⟩ ⟨sc, F.H.W + 48 + F.H.FD⟩)
    (d_os : Region.Disjoint ⟨o, F.H.D⟩ ⟨sc, F.H.W + 48 + F.H.FD⟩)
    (b_i : (below s.sp 96).Disjoint ⟨inn, F.H.S⟩) (b_u : (below s.sp 96).Disjoint ⟨ou, F.H.S⟩)
    (b_o : (below s.sp 96).Disjoint ⟨o, F.H.D⟩) (b_s : (below s.sp 96).Disjoint ⟨sc, F.H.W + 48 + F.H.FD⟩)
    (hc : Covers ([⟨ou, F.H.S⟩] ++ [⟨inn, F.H.S⟩, ⟨o, F.H.D⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨inn, F.H.S⟩, ⟨o, F.H.D⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩] s.wr) {Q : State → Prop}
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
  have c4 : s.callEntry.gpr .r4 = ou := (State.callEntry_gpr _ (by decide)).trans h4
  have c3 : s.callEntry.gpr .r3 = inn := (State.callEntry_gpr _ (by decide)).trans h3
  have c5 : s.callEntry.gpr .r5 = s.gpr .r5 := State.callEntry_gpr _ (by decide)
  have c6 : s.callEntry.gpr .r6 = o := (State.callEntry_gpr _ (by decide)).trans h6
  have c7 : s.callEntry.gpr .r7 = sc := (State.callEntry_gpr _ (by decide)).trans h7
  refine WP.callF (k := finG hF.hH.SH (F.H.W + 48 + F.H.FD) 96)
    (fun s hs => by
      obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.PPC64LE.Finalize.correct hF.hH hs
      exact ⟨t, s', he, h₁, h₂⟩)
    (rd := [⟨ou, hF.hH.SH.stateBytes⟩])
    (wr := [⟨inn, hF.hH.SH.stateBytes⟩, ⟨o, hF.hH.SH.digestBytes⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩]) ?_
    (by rw [hS, hD]; exact hc) (by rw [hS, hD]; exact hw) ?_ (by omega) hpf
  · simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3, c4, c6, c7, hS, hD]
    exact ⟨trivial, trivial, d_iu, d_io, d_is, d_uo, d_us, d_os, hsp, b_i, b_u, b_o, b_s⟩
  · intro s' hrd hwr hsp' hf hcs hpost
    simp only [finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6,
      hD, hB] at hpost
    refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
    rw [hS, hD] at hf
    exact Frame.below_mono hf (by omega) (by omega)

include hF in
/-- `iterate` with the key's states at `key`, `U` at `u`, `n` in `r5`, `T` at
`t` and the working space at `sc`. -/
theorem it_call {s : State} {key u t sc : Addr}
    (h3 : s.gpr .r3 = key) (h4 : s.gpr .r4 = u) (h6 : s.gpr .r6 = t) (h7 : s.gpr .r7 = sc)
    (hsp : 96 ≤ s.sp.toNat)
    (d_kt : Region.Disjoint ⟨key, 2 * F.H.S⟩ ⟨t, F.H.D⟩)
    (d_ks : Region.Disjoint ⟨key, 2 * F.H.S⟩ ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩)
    (d_ut : Region.Disjoint ⟨u, F.H.D⟩ ⟨t, F.H.D⟩)
    (d_us : Region.Disjoint ⟨u, F.H.D⟩ ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩)
    (d_ts : Region.Disjoint ⟨t, F.H.D⟩ ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩)
    (b_k : (below s.sp 96).Disjoint ⟨key, 2 * F.H.S⟩) (b_u : (below s.sp 96).Disjoint ⟨u, F.H.D⟩)
    (b_t : (below s.sp 96).Disjoint ⟨t, F.H.D⟩)
    (b_s : (below s.sp 96).Disjoint ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩)
    (hc : Covers ([⟨key, 2 * F.H.S⟩, ⟨u, F.H.D⟩] ++ [⟨t, F.H.D⟩, ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩])
      (s.rd ++ s.wr))
    (hw : Covers [⟨t, F.H.D⟩, ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩] s.wr) {Q : State → Prop}
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
  have c3 : s.callEntry.gpr .r3 = key := (State.callEntry_gpr _ (by decide)).trans h3
  have c4 : s.callEntry.gpr .r4 = u := (State.callEntry_gpr _ (by decide)).trans h4
  have c5 : s.callEntry.gpr .r5 = s.gpr .r5 := State.callEntry_gpr _ (by decide)
  have c6 : s.callEntry.gpr .r6 = t := (State.callEntry_gpr _ (by decide)).trans h6
  have c7 : s.callEntry.gpr .r7 = sc := (State.callEntry_gpr _ (by decide)).trans h7
  refine WP.callF (k := iterG hF.hH.SH (Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H) 96)
    (fun s hs => by
      obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Pbkdf2.Stream.PPC64LE.Iter.correct hF.hH hs
      exact ⟨t, s', he, h₁, h₂⟩)
    (rd := [⟨key, 2 * hF.hH.SH.stateBytes⟩, ⟨u, hF.hH.SH.digestBytes⟩])
    (wr := [⟨t, hF.hH.SH.digestBytes⟩, ⟨sc, Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H⟩]) ?_
    (by rw [hS, hD]; exact hc) (by rw [hD]; exact hw) ?_ (by omega) hpf
  · simp only [iterG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3, c4, c6, c7, hS, hD]
    exact ⟨trivial, trivial, d_kt, d_ks, d_ut, d_us, d_ts, hsp, b_k, b_u, b_t, b_s⟩
  · intro s' hrd hwr hsp' hf hcs hpost
    simp only [iterG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6,
      hD, hB, hS] at hpost
    refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
    rw [hD] at hf
    exact Frame.below_mono hf (by omega) (by omega)

/-- The streaming `update`, as `HashOK.callUpd_ok` gives it. -/
theorem upd_call (hH : HashOK F.H) {s : State} {st dat sc : Addr} {len : Nat}
    (h3 : s.gpr .r3 = st) (h5 : s.gpr .r5 = dat) (h6 : (s.gpr .r6).toNat = len) (h7 : s.gpr .r7 = sc)
    (hd₁ : Region.Disjoint ⟨st, F.H.S⟩ ⟨sc, F.H.W⟩) (hd₂ : Region.Disjoint ⟨dat, len⟩ ⟨st, F.H.S⟩)
    (hd₃ : Region.Disjoint ⟨dat, len⟩ ⟨sc, F.H.W⟩) (hsp : 48 ≤ s.sp.toNat)
    (hs₁ : (below s.sp 48).Disjoint ⟨st, F.H.S⟩) (hs₂ : (below s.sp 48).Disjoint ⟨dat, len⟩)
    (hs₃ : (below s.sp 48).Disjoint ⟨sc, F.H.W⟩)
    (hc : Covers ([⟨dat, len⟩] ++ [⟨st, F.H.S⟩, ⟨sc, F.H.W⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, F.H.S⟩, ⟨sc, F.H.W⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨st, F.H.S⟩, ⟨sc, F.H.W⟩] ++ [below s.sp 48]) s' →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .r4 = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem dat len)) → Q s') :
    WP isa F.H.callUpd s Q :=
  hH.callUpd_ok h3 h5 h6 h7 hd₁ hd₂ hd₃ hsp hs₁ hs₂ hs₃ hc hw fun s' a b c d e f => hQ s' ⟨a, b, c, e, d⟩ f

end VG.Proof.Pbkdf2.Whole.PPC64LE
