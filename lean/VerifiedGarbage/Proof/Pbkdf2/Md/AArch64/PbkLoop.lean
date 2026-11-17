module

import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Common
import VerifiedGarbage.Proof.Sha256.Stream

/-! ### `Pbkdf2.Md.AArch64.Pbkdf2`, which this module and modules that import it used -/

section

/-! ### `Pbkdf2.Md.AArch64.PbkCalls`, which only this module used -/

section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`'s calls

The calls of HMAC's `init` and `finalize` and of `iterate`, whose contracts
(`initG`, `finG`, `iterK`) their proofs are given as hypotheses: each is run
with `WP.callFV` (the callee may use the 16 bytes below the stack pointer, a
frame deep), and shown constant time in two runs with `RelCT.call`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.AArch64 (iterK)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG After frame_depth fdepth_lt ce0 ce1 ce2 ce3 ce4)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash} (hH : HashOK H)

theorem covers_app {rd wr : List Region} {s : State} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ wr) (s.rd ++ s.wr) := fun a n hi => by
  obtain ⟨r, hr', hc⟩ := hi
  rcases List.mem_append.mp hr' with h | h
  · exact hr a n ⟨r, h, hc⟩
  · obtain ⟨r'', h'', hc''⟩ := hw a n ⟨r, h, hc⟩
    exact ⟨r'', List.mem_append_right _ h'', hc''⟩

/-! ## HMAC's `init` -/

/-- The regions of a call of HMAC's `init`. -/
structure InitArgs (s : State) (inn out k sc : Addr) (kl : Nat) : Prop where
  x0 : s.gpr .x0 = inn
  x1 : s.gpr .x1 = out
  x2 : s.gpr .x2 = k
  x3 : (s.gpr .x3).toNat = kl
  x4 : s.gpr .x4 = sc
  klB : kl ≤ H.P.B
  cr : Covers [⟨k, kl⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨out, H.S⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨out, H.S⟩ ⟨sc, 8 * H.W⟩
  k_i : Region.Disjoint ⟨k, kl⟩ ⟨inn, H.S⟩
  k_o : Region.Disjoint ⟨k, kl⟩ ⟨out, H.S⟩
  k_s : Region.Disjoint ⟨k, kl⟩ ⟨sc, 8 * H.W⟩
  sp16 : 16 ≤ s.sp.toNat
  stk_i : (below s.sp 16).Disjoint ⟨inn, H.S⟩
  stk_o : (below s.sp 16).Disjoint ⟨out, H.S⟩
  stk_k : (below s.sp 16).Disjoint ⟨k, kl⟩
  stk_s : (below s.sp 16).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem InitArgs.pre {s : State} {inn out k sc : Addr} {kl : Nat} (a : InitArgs (H := H) s inn out k sc kl) :
    (initG hH.SH H.W).pre (s.callEntry.withRegions [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩]) := by
  obtain hS := hH.hS; have hB := hH.hB
  simp only [initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ce0, ce1, ce2, ce3, ce4, a.x0, a.x1, a.x2, a.x3, a.x4, hS, hB]
  exact ⟨a.klB, trivial, trivial, a.i_o, a.i_s, a.o_s, a.k_i, a.k_o, a.k_s, a.sp16, a.stk_i, a.stk_o, a.stk_k,
    a.stk_s, a.scnw⟩

theorem hinit_call (hv : Verified AArch64.target H.hmacInit (initG hH.SH H.W)) (hd : H.hmacInit.aarch64Depth ≤ 1)
    {s : State} {inn out k sc : Addr} {kl : Nat} (a : InitArgs (H := H) s inn out k sc kl) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] s' →
      hH.SH.Repr s'.mem inn (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) ipad) →
      hH.SH.Repr s'.mem out (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa (.call H.hmacInitN H.hmacInit) s Q := by
  refine WP.of_syms (WP.callFV hv.1 (a.pre hH) (covers_app a.cr a.cw) a.cw ?_ (fdepth_lt hd))
  intro s' h₁ h₂ h₃ h₄ h₅ hvec hpost hsy
  simp only [initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, ce1, ce2, ce3,
    a.x0, a.x1, a.x2, a.x3] at hpost
  exact hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hd h₄, hvec, hsy⟩ hpost.1 hpost.2

theorem hinit_rel (hv : Verified AArch64.target H.hmacInit (initG hH.SH H.W)) {P : State → State → Prop}
    {inn out k sc : Addr} {kl : Nat}
    (h : ∀ s s', P s s' → InitArgs (H := H) s inn out k sc kl ∧ InitArgs (H := H) s' inn out k sc kl ∧
      s.sp = s'.sp) :
    RelCT isa P (.call H.hmacInitN H.hmacInit) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  obtain x3 : s.gpr .x3 = s'.gpr .x3 := BitVec.eq_of_toNat_eq (by rw [a.x3, a'.x3])
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw⟩
  simp only [initG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, ce0, ce1, ce2, ce3, ce4,
    a.x0, a'.x0, a.x1, a'.x1, a.x2, a'.x2, a.x4, a'.x4, x3, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## HMAC's `finalize` -/

/-- The regions of a call of HMAC's `finalize`. -/
structure FinArgs (s : State) (inn outer cnt o sc : Addr) : Prop where
  x0 : s.gpr .x0 = inn
  x1 : s.gpr .x1 = outer
  x2 : s.gpr .x2 = cnt
  x3 : s.gpr .x3 = o
  x4 : s.gpr .x4 = sc
  cr : Covers [⟨outer, H.S⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_u : Region.Disjoint ⟨inn, H.S⟩ ⟨outer, H.S⟩
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨o, H.D⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  u_o : Region.Disjoint ⟨outer, H.S⟩ ⟨o, H.D⟩
  u_s : Region.Disjoint ⟨outer, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨o, H.D⟩ ⟨sc, 8 * H.W⟩
  sp16 : 16 ≤ s.sp.toNat
  stk_i : (below s.sp 16).Disjoint ⟨inn, H.S⟩
  stk_u : (below s.sp 16).Disjoint ⟨outer, H.S⟩
  stk_o : (below s.sp 16).Disjoint ⟨o, H.D⟩
  stk_s : (below s.sp 16).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem FinArgs.pre {s : State} {inn outer cnt o sc : Addr} (a : FinArgs (H := H) s inn outer cnt o sc) :
    (finG hH.SH H.W).pre (s.callEntry.withRegions [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  obtain hS := hH.hS; have hD := hH.hD
  simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ce0, ce1, ce3, ce4, a.x0, a.x1, a.x3, a.x4, hS, hD]
  exact ⟨trivial, trivial, a.i_u, a.i_o, a.i_s, a.u_o, a.u_s, a.o_s, a.sp16, a.stk_i, a.stk_u, a.stk_o,
    a.stk_s, a.scnw⟩

theorem hfin_call (hv : Verified AArch64.target H.hmacFin (finG hH.SH H.W)) (hd : H.hmacFin.aarch64Depth ≤ 1)
    {s : State} {inn outer cnt o sc : Addr}
    (a : FinArgs (H := H) s inn outer cnt o sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] s' →
      (∀ k0 text, k0.length = H.P.B → k0.length + text.length < 2 ^ 64 →
        hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) → cnt = BitVec.ofNat 64 (H.P.B + text.length) →
        hH.SH.Repr s.mem outer (xorPad k0 opad) → bytesAt s'.mem o H.D = hmacBlockKey hH.SH.H k0 text) →
      Q s') :
    WP isa (.call H.hmacFinN H.hmacFin) s Q := by
  refine WP.of_syms (WP.callFV hv.1 (a.pre hH) (covers_app a.cr a.cw) a.cw ?_ (fdepth_lt hd))
  intro s' h₁ h₂ h₃ h₄ h₅ hvec hpost hsy
  refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hd h₄, hvec, hsy⟩ fun k0 text hk hl hi hc ho => ?_
  obtain hD := hH.hD; have hB := hH.hB
  simp only [finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, ce1, ce2, ce3,
    a.x0, a.x1, a.x2, a.x3, hD, hB] at hpost
  exact hpost k0 text hk hl hi hc ho

theorem hfin_rel (hv : Verified AArch64.target H.hmacFin (finG hH.SH H.W)) {P : State → State → Prop}
    {inn outer cnt o sc : Addr}
    (h : ∀ s s', P s s' → FinArgs (H := H) s inn outer cnt o sc ∧ FinArgs (H := H) s' inn outer cnt o sc ∧
      s.sp = s'.sp) :
    RelCT isa P (.call H.hmacFinN H.hmacFin) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw⟩
  simp only [finG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, ce0, ce1, ce2, ce3, ce4,
    a.x0, a'.x0, a.x1, a'.x1, a.x2, a'.x2, a.x3, a'.x3, a.x4, a'.x4, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `iterate` -/

/-- The regions of a call of `iterate`. -/
structure IterArgs (s : State) (key u : Addr) (n : BitVec 64) (t sc : Addr) : Prop where
  x0 : s.gpr .x0 = key
  x1 : s.gpr .x1 = u
  x2 : s.gpr .x2 = n
  x3 : s.gpr .x3 = t
  x4 : s.gpr .x4 = sc
  cr : Covers [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] (s.rd ++ s.wr)
  cw : Covers [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  k_t : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨t, H.D⟩
  k_s : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨sc, 8 * H.W⟩
  u_t : Region.Disjoint ⟨u, H.D⟩ ⟨t, H.D⟩
  u_s : Region.Disjoint ⟨u, H.D⟩ ⟨sc, 8 * H.W⟩
  t_s : Region.Disjoint ⟨t, H.D⟩ ⟨sc, 8 * H.W⟩
  knw : key.toNat + 2 * H.S ≤ 2 ^ 64
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem IterArgs.pre {s : State} {key u t sc : Addr} {n : BitVec 64} (a : IterArgs (H := H) s key u n t sc) :
    (iterK hH.SH H.W).pre (s.callEntry.withRegions [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  obtain hS := hH.hS; have hD := hH.hD
  simp only [iterK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, ce0, ce1, ce3, ce4,
    a.x0, a.x1, a.x3, a.x4, hS, hD]
  exact ⟨trivial, trivial, a.k_t, a.k_s, a.u_t, a.u_s, a.t_s, a.knw, a.scnw⟩

theorem iter_call (hv : Verified AArch64.target H.iterate (iterK hH.SH H.W)) (hd : H.iterate.aarch64Depth ≤ 1)
    {s : State} {key u t sc : Addr} {n : BitVec 64}
    (a : IterArgs (H := H) s key u n t sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] s' →
      (∀ k0, k0.length = H.P.B → hH.SH.Repr s.mem key (xorPad k0 ipad) →
        hH.SH.Repr s.mem (key + BitVec.ofNat 64 H.S) (xorPad k0 opad) →
        bytesAt s'.mem t H.D = Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (n.setWidth 32).toNat
          (bytesAt s.mem u H.D) (bytesAt s.mem t H.D)) →
      Q s') :
    WP isa (.call H.iterN H.iterate) s Q := by
  refine WP.of_syms (WP.callFV hv.1 (a.pre hH) (covers_app a.cr a.cw) a.cw ?_ (fdepth_lt hd))
  intro s' h₁ h₂ h₃ h₄ h₅ hvec hpost hsy
  refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hd h₄, hvec, hsy⟩ fun k0 hk hi ho => ?_
  obtain hS := hH.hS; have hD := hH.hD; have hB := hH.hB
  simp only [iterK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, ce1, ce2, ce3,
    a.x0, a.x1, a.x2, a.x3, hD, hB, hS] at hpost
  exact hpost k0 hk hi ho

theorem iter_rel (hv : Verified AArch64.target H.iterate (iterK hH.SH H.W)) {P : State → State → Prop}
    {key u t sc : Addr} {n : BitVec 64}
    (h : ∀ s s', P s s' → IterArgs (H := H) s key u n t sc ∧ IterArgs (H := H) s' key u n t sc ∧
      s.sp = s'.sp) :
    RelCT isa P (.call H.iterN H.iterate) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw⟩
  simp only [iterK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, ce0, ce1, ce2, ce3, ce4,
    a.x0, a'.x0, a.x1, a'.x1, a.x2, a'.x2, a.x3, a'.x3, a.x4, a'.x4, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.Pbkdf2.Md.AArch64.Pbk

end

end

/-! ### `Pbkdf2.Md.AArch64.PbkCommon`, which only this module used -/

section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`'s parts

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/PbkCommon.lean`): the precondition of
`pbkdf2` (`Pre`), the parts of its `scratch`, and what every piece of it keeps
(`KR`): our caller's registers (those we save in `scratch`, and `x25`–`x28`,
which nothing we run writes), `out`, `c - 1` and `out_len` in `scratch`, and
that everything written is in `out`, `scratch` or the 16 bytes below the stack
pointer.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK pbkG)
open VG.Proof.Pbkdf2.AArch64 (Sizes)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (stk SavedRegs SavedRegs.frame saveR)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep sub_of_off sub_of_self)
open Spec.Sha256 (bytesAt)

variable {H : Hash}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev pw : Addr := s₀.gpr .x0
abbrev pwl : Nat := (s₀.gpr .x1).toNat
abbrev salt : Addr := s₀.gpr .x2
abbrev sl : Nat := (s₀.gpr .x3).toNat
/-- The iteration count. -/
abbrev cc : Nat := ((s₀.gpr .x4).setWidth 32).toNat
abbrev out : Addr := s₀.gpr .x5
abbrev ol : Nat := (s₀.gpr .x6).toNat
abbrev scr : Addr := s₀.gpr .x7
abbrev pwR : Region := ⟨pw s₀, pwl s₀⟩
abbrev saltR : Region := ⟨salt s₀, sl s₀⟩
abbrev outR : Region := ⟨out s₀, ol s₀⟩
abbrev scR : Region := ⟨scr s₀, (H.W + H.S) * 8⟩
abbrev stkR : Region := stk s₀
/-- An address in `scratch`, and a part of it. -/
abbrev A (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- Our caller's registers, `out`, `c - 1` and `out_len`. -/
abbrev hdrR : Region := sR s₀ H.sv 80
/-- The working space of the functions we call. -/
abbrev lowR : Region := ⟨scr s₀, 8 * H.W⟩

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  rd : s₀.rd = [pwR s₀, saltR s₀]
  wr : s₀.wr = [outR s₀, scR (H := H) s₀]
  pw_o : (pwR s₀).Disjoint (outR s₀)
  pw_s : (pwR s₀).Disjoint (scR (H := H) s₀)
  sa_o : (saltR s₀).Disjoint (outR s₀)
  sa_s : (saltR s₀).Disjoint (scR (H := H) s₀)
  o_s : (outR s₀).Disjoint (scR (H := H) s₀)
  stk_pw : (stkR s₀).Disjoint (pwR s₀)
  stk_sa : (stkR s₀).Disjoint (saltR s₀)
  stk_o : (stkR s₀).Disjoint (outR s₀)
  stk_s : (stkR s₀).Disjoint (scR (H := H) s₀)
  pwnw : (pw s₀).toNat + pwl s₀ ≤ 2 ^ 64
  sanw : (salt s₀).toNat + sl s₀ ≤ 2 ^ 64
  onw : (out s₀).toNat + ol s₀ ≤ 2 ^ 64
  snw : (scr s₀).toNat + (H.W + H.S) * 8 ≤ 2 ^ 64
  c0 : 0 < cc s₀
  olD : ol s₀ ≤ (2 ^ 32 - 1) * H.D

theorem pre_of (hH : HashOK H) {s₀ : State} (h : (pbkG hH.SH (H.W + H.S)).pre s₀) : Pre (H := H) s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have hD := hH.hD
  simp only [hD] at h17
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- The sizes, as facts about natural numbers. -/
structure PSizes (H : Hash) : Prop where
  z : Sizes H.P H.D H.W
  W : H.W ≤ 256

theorem _root_.VG.Proof.Pbkdf2.Md.AArch64.HashOK.psizes (hH : HashOK H) : PSizes H := ⟨hH.sizes, hH.W⟩

theorem PSizes.N (hz : PSizes H) : 0 < H.P.N ∧ H.P.N ≤ 64 := hz.z.dims.N
theorem PSizes.B_le (hz : PSizes H) : H.P.B ≤ 128 := by rcases hz.z.B with h | h <;> omega_using [h]
theorem PSizes.B_ge (hz : PSizes H) : 64 ≤ H.P.B := by rcases hz.z.B with h | h <;> omega_using [h]

/-! ## The parts of `scratch` -/

/-- Where the parts of `scratch` are. -/
theorem layout : H.sv = 8 * H.W ∧ H.outO = 8 * H.W + 56 ∧ H.cO = 8 * H.W + 64 ∧ H.olO = 8 * H.W + 72 ∧
    H.st0O = 8 * H.W + 80 ∧ H.st1O = 8 * H.W + 80 + H.S ∧ H.stSO = 8 * H.W + 80 + 2 * H.S ∧
    H.stWO = 8 * H.W + 80 + 3 * H.S ∧ H.uO = 8 * H.W + 80 + 4 * H.S ∧
    H.tO = 8 * H.W + 80 + 4 * H.S + H.D ∧ H.hkO = 8 * H.W + 80 + 4 * H.S + 2 * H.D ∧
    H.intO = 8 * H.W + 80 + 4 * H.S + 2 * H.D + H.P.N ∧ H.S = H.P.N + H.P.B := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [Hash.sv, Hash.st0O, Hash.st1O, Hash.stSO, Hash.stWO, Hash.uO, Hash.tO,
      Hash.hkO, Hash.intO] <;> omega_using []

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)

include hz in
/-- The parts of `scratch`, as offsets: they end before its end, and below
4096 (every offset is an immediate). -/
theorem end_le : H.intO + 4 ≤ (H.W + H.S) * 8 ∧ H.intO + 4 ≤ 4096 := by
  have := hz.N; have := hz.z.DN; have := hz.B_le; have := hz.B_ge; have := hz.W; have := layout (H := H)
  omega_arith

include hz in
theorem L_lt : (H.W + H.S) * 8 < 2 ^ 64 := by
  have := hz.W; have := hz.N; have := hz.B_le; show (H.W + (H.P.N + H.P.B)) * 8 < 2 ^ 64; omega_arith

theorem part_sub {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) : Region.Sub (sR s₀ o n) (scR (H := H) s₀) :=
  Offset.sub_base _ h

include hz in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ (H.W + H.S) * 8)
    (hb : b + n ≤ (H.W + H.S) * 8) : Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := L_lt hz; exact Offset.disjoint _ h (by omega_using [ha, this]) (by omega_using [hb, this])

include hz in
theorem low_disj {b n : Nat} (hb : 8 * H.W ≤ b) (hbn : b + n ≤ (H.W + H.S) * 8) :
    Region.Disjoint (sR s₀ b n) (lowR (H := H) s₀) := by
  have := L_lt hz; exact Offset.disjoint_base _ hb (by omega_using [hbn, this])

theorem low_sub : Region.Sub (lowR (H := H) s₀) (scR (H := H) s₀) :=
  Region.sub_prefix (by show 8 * H.W ≤ (H.W + H.S) * 8; omega_using [])

include hp hz in
theorem in_sc {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) :
    InRegions s.wr (A s₀ o) n := by
  have := L_lt hz
  exact ⟨scR (H := H) s₀, by rw [hwr, hp.wr]; simp, Offset.contains_base _ h (by omega_using [h, this])⟩

include hp in
theorem sc_mem : scR (H := H) s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the entry on: our caller's registers,
`out`, `c - 1` and `out_len` in `scratch`, and everything written is in
`out`, `scratch` or the 16 bytes below the stack pointer. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x23 : s.gpr .x23 = scr s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H.hh (scr s₀) s₀ s.mem
  outW : s.mem.readW (A s₀ H.outO) 64 = out s₀
  cW : s.mem.readW (A s₀ H.cO) 64 = BitVec.ofNat 64 (cc s₀ - 1)
  olW : s.mem.readW (A s₀ H.olO) 64 = s₀.gpr .x6
  frame : Frame [outR s₀, scR (H := H) s₀, stkR s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.x23, .x25, .x26, .x27, .x28]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem hdr_sub {s₀ : State} {o : Nat} (h₁ : H.sv ≤ o) (h₂ : o + 8 ≤ H.sv + 80) :
    Region.Sub ⟨A s₀ o, 8⟩ (hdrR (H := H) s₀) := Offset.sub _ h₁ h₂

theorem save_hdr {s₀ : State} : Region.Sub (saveR H.hh (scr s₀)) (hdrR (H := H) s₀) :=
  Offset.sub _ (Nat.le_refl _) (by show 8 * H.W + 56 ≤ 8 * H.W + 80; omega_using [])

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp hz in
theorem KR.keep {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (hdrR (H := H) s₀).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [outR s₀, scR (H := H) s₀, stkR s₀], Region.Sub r r') :
    KR (H := H) s₀ s' := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x23,
    fun r hr => (hg r (by revert hr; decide +revert)).trans (h.cs r hr),
    SavedRegs.frame H.hh h.saved hf fun r hr => (hd r hr).sub_left save_hdr, ?_, ?_, ?_,
    h.frame.trans (hf.sub hsub)⟩
  · rw [← h.outW]
    exact hf.readW (r := ⟨A s₀ H.outO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.outO]) (by simp [Hash.outO])))
      (by decide)
  · rw [← h.cW]
    exact hf.readW (r := ⟨A s₀ H.cO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.cO]) (by simp [Hash.cO])))
      (by decide)
  · rw [← h.olW]
    exact hf.readW (r := ⟨A s₀ H.olO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.olO]) (by simp [Hash.olO])))
      (by decide)

omit hp hz in
theorem KR.same {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (hm ▸ Frame.refl [] s.mem) (fun _ h => by simp at h)
    (fun _ h => by simp at h)

omit hp hz in
theorem KR.upd {s s' : State} (h : KR (H := H) s₀ s) {d : Reg} {v : BitVec 64}
    (u : VG.Proof.MdStream.AArch64.Upd s s' d v) (hd : d ∉ kregs) : KR (H := H) s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

omit hp in
/-- A write into a part of `scratch` after its header keeps `KR`. -/
theorem KR.write {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {o n : Nat}
    (ho : H.st0O ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [sR s₀ o n] s.mem s'.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp hg hf
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by simpa [Hash.st0O] using ho)) (by
        have := (end_le hz).1; simp only [Hash.st0O] at ho; omega_using [ho, hon]) hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, part_sub hon⟩)

omit hz in
theorem stk_sc {s : State} (h : KR (H := H) s₀ s) {R : Region} (hR : Region.Sub R (scR (H := H) s₀)) :
    (below s.sp 16).Disjoint R := by
  rw [h.sp]; exact hp.stk_s.sub_right hR

/-- What a call leaves, writing parts of `scratch` after its header, or its
working space, and the 16 bytes below the stack pointer. -/
theorem KR.call {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hcs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) {ws : List Region}
    (hf : Frame (ws ++ [below s.sp 16]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) :
    KR (H := H) s₀ s' := by
  have := (end_le hz).1; have := layout (H := H)
  obtain hst : H.sv + 80 = H.st0O := by simp [Hash.st0O]
  refine h.keep hrd hwr hsp (fun r hr => hcs r (kregs_pres r hr).1 (kregs_pres r hr).2) hf
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact (low_disj hz (Nat.le_refl _) (by omega_arith)).sub_right (Region.sub_prefix hk)
      · exact part_disj hz (Or.inl (by rw [hst]; exact h₁)) (by rw [hst]; omega_using [h₁, h₂]) h₂
    · simp only [List.mem_singleton] at hr; subst hr
      exact (stk_sc hp h (part_sub (by rw [hst]; omega_arith))).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact ⟨scR (H := H) s₀, by simp, Region.sub_prefix (by show k ≤ (H.W + H.S) * 8; omega_using [hk])⟩
      · exact ⟨_, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.sp]
      exact ⟨_, by simp, fun _ h => h⟩

omit hp hz in
/-- The regions only read are the same as on entry. -/
theorem KR.bytes {s : State} (h : KR (H := H) s₀ s) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ [outR s₀, scR (H := H) s₀, stkR s₀], Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    bytesAt s.mem p n = bytesAt s₀.mem p n :=
  bytes_keep h.frame hd hn

omit hz in
theorem KR.pwBytes {s : State} (h : KR (H := H) s₀ s) :
    bytesAt s.mem (pw s₀) (pwl s₀) = bytesAt s₀.mem (pw s₀) (pwl s₀) :=
  h.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.pw_o
    · exact hp.pw_s
    · exact hp.stk_pw.symm) (by have := hp.pwnw; omega_using [this])

omit hz in
theorem KR.saltBytes {s : State} (h : KR (H := H) s₀ s) :
    bytesAt s.mem (salt s₀) (sl s₀) = bytesAt s₀.mem (salt s₀) (sl s₀) :=
  h.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.stk_sa.symm) (by have := hp.sanw; omega_using [this])

omit hz in
theorem in_wr {s : State} (h : KR (H := H) s₀ s) : scR (H := H) s₀ ∈ s.wr := by rw [h.wr]; exact sc_mem hp

omit hz in
/-- The parts of `scratch` the functions we call get, as covered regions. -/
theorem cov_part {s : State} (h : KR (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  sub_of_off (in_wr hp h) hon

omit hz in
theorem cov_low {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (⟨scr s₀, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨scr s₀, n⟩ : Region).len ≤ r'.len :=
  sub_of_self (in_wr hp h) hn

/-- A part of `scratch`, readable. -/
theorem in_rw {s : State} (h : KR (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ (H.W + H.S) * 8) :
    InRegions (s.rd ++ s.wr) (A s₀ o) n :=
  VG.Proof.Hmac.Generic.Common.InRegions.right' ⟨_, in_wr hp h, Offset.contains_base _ hon
    (by have := L_lt hz; omega_using [hon, this])⟩

end

/-! ## Facts about the offsets

Each proved once, by `omega` on `layout`, for the step proofs: an `omega`
over a step's context, which holds many facts about states and sizes, costs
far more. -/

theorem PSizes.B4 (hz : PSizes H) : H.P.B % 4 = 0 := by rcases hz.z.B with h | h <;> omega_using [h]
theorem PSizes.o_B_4_lt_4096 (hz : PSizes H) : H.P.B + 4 < 4096 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_B_lt_4096 (hz : PSizes H) : H.P.B < 4096 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_B_lt_p64 (hz : PSizes H) : H.P.B < 2 ^ 64 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_le_p64 (hz : PSizes H) : H.D ≤ 2 ^ 64 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_lt_4096 (hz : PSizes H) : H.D < 4096 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_lt_p16 (hz : PSizes H) : H.D < 2 ^ 16 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_lt_p64 (hz : PSizes H) : H.D < 2 ^ 64 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_W8_56_le_L (hz : PSizes H) : 8 * H.W + 56 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_W8_56_le_outO (hz : PSizes H) : 8 * H.W + 56 ≤ H.outO := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_W8_le_L (hz : PSizes H) : 8 * H.W ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_using []
theorem PSizes.o_W8_le_hkO (hz : PSizes H) : 8 * H.W ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_W8_le_intO (hz : PSizes H) : 8 * H.W ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_W8_le_st0O (hz : PSizes H) : 8 * H.W ≤ H.st0O := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_W8_le_st1O (hz : PSizes H) : 8 * H.W ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_W8_le_stSO (hz : PSizes H) : 8 * H.W ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_W8_le_stWO (hz : PSizes H) : 8 * H.W ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_W8_le_sv (hz : PSizes H) : 8 * H.W ≤ H.sv := by
  simp only [Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_W8_le_tO (hz : PSizes H) : 8 * H.W ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_W8_le_uO (hz : PSizes H) : 8 * H.W ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_cO_64d8_le_outO_24 (hz : PSizes H) : H.cO + 64 / 8 ≤ H.outO + 24 := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_cO_8_le_L (hz : PSizes H) : H.cO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.cO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_cO_8_le_olO (hz : PSizes H) : H.cO + 8 ≤ H.olO := by
  simp only [Hash.cO, Hash.olO, Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_hkO_D_le_L (hz : PSizes H) : H.hkO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_hkO_hsF_le_L (hz : PSizes H) : H.hkO + H.stream.F ≤ (H.W + H.S) * 8 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; have : H.stream.F = H.P.N := rfl; omega_arith
theorem PSizes.o_hkO_lt_4096 (hz : PSizes H) : H.hkO < 4096 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_intO_4_le_L (hz : PSizes H) : H.intO + 4 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_intO_lt_4096 (hz : PSizes H) : H.intO < 4096 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_olO_64d8_le_outO_24 (hz : PSizes H) : H.olO + 64 / 8 ≤ H.outO + 24 := by
  simp only [Hash.outO, Hash.olO, Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_olO_8_le_L (hz : PSizes H) : H.olO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.olO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_outO_24_le_L (hz : PSizes H) : H.outO + 24 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.outO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_outO_24_lt_p64 (hz : PSizes H) : H.outO + 24 < 2 ^ 64 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_outO_64d8_le_outO_24 (hz : PSizes H) : H.outO + 64 / 8 ≤ H.outO + 24 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_outO_8_le_L (hz : PSizes H) : H.outO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.outO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_outO_8_le_cO (hz : PSizes H) : H.outO + 8 ≤ H.cO := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_outO_8_le_olO (hz : PSizes H) : H.outO + 8 ≤ H.olO := by
  simp only [Hash.outO, Hash.olO, Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_outO_le_cO (hz : PSizes H) : H.outO ≤ H.cO := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_outO_le_olO (hz : PSizes H) : H.outO ≤ H.olO := by
  simp only [Hash.outO, Hash.olO, Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_st0O_2mS_le_L (hz : PSizes H) : H.st0O + 2 * H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_st0O_2mS_le_tO (hz : PSizes H) : H.st0O + 2 * H.S ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st0O_3mS_le_L (hz : PSizes H) : H.st0O + 3 * H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_st0O_S_le_L (hz : PSizes H) : H.st0O + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_st0O_S_le_hkO (hz : PSizes H) : H.st0O + H.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st0O_S_le_st0O_3mS (hz : PSizes H) : H.st0O + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st0O_S_le_st1O (hz : PSizes H) : H.st0O + H.S ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st0O_S_le_stSO (hz : PSizes H) : H.st0O + H.S ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st0O_le_st0O (hz : PSizes H) : H.st0O ≤ H.st0O := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.DN; omega_using []
theorem PSizes.o_st0O_le_st1O (hz : PSizes H) : H.st0O ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st0O_le_stSO (hz : PSizes H) : H.st0O ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st0O_lt_4096 (hz : PSizes H) : H.st0O < 4096 := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_st0O_lt_p64 (hz : PSizes H) : H.st0O < 2 ^ 64 := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_st1O_S_le_L (hz : PSizes H) : H.st1O + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_st1O_S_le_hkO (hz : PSizes H) : H.st1O + H.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st1O_S_le_st0O_3mS (hz : PSizes H) : H.st1O + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st1O_S_le_stSO (hz : PSizes H) : H.st1O + H.S ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st1O_S_le_stWO (hz : PSizes H) : H.st1O + H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st1O_S_le_uO (hz : PSizes H) : H.st1O + H.S ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st1O_lt_4096 (hz : PSizes H) : H.st1O < 4096 := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_stSO_S_le_L (hz : PSizes H) : H.stSO + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_stSO_S_le_st0O_3mS (hz : PSizes H) : H.stSO + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_stSO_S_le_stWO (hz : PSizes H) : H.stSO + H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_stSO_hsS_le_L (hz : PSizes H) : H.stSO + H.stream.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stSO_lt_4096 (hz : PSizes H) : H.stSO < 4096 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_stWO_S_le_L (hz : PSizes H) : H.stWO + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_stWO_S_le_intO (hz : PSizes H) : H.stWO + H.S ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_stWO_S_le_uO (hz : PSizes H) : H.stWO + H.S ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_stWO_hsS_le_L (hz : PSizes H) : H.stWO + H.stream.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stWO_hsS_le_hkO (hz : PSizes H) : H.stWO + H.stream.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stWO_hsS_le_intO (hz : PSizes H) : H.stWO + H.stream.S ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stWO_le_intO (hz : PSizes H) : H.stWO ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_stWO_le_tO (hz : PSizes H) : H.stWO ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_stWO_lt_4096 (hz : PSizes H) : H.stWO < 4096 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_sv_80_le_L (hz : PSizes H) : H.sv + 80 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_tO_D_le_L (hz : PSizes H) : H.tO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_tO_lt_4096 (hz : PSizes H) : H.tO < 4096 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_uO_D_le_L (hz : PSizes H) : H.uO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_uO_D_le_tO (hz : PSizes H) : H.uO + H.D ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_uO_lt_4096 (hz : PSizes H) : H.uO < 4096 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_outO_mod_8_eq_0 (_hz : PSizes H) : H.outO % 8 = 0 := by
  simp only [Hash.outO, Hash.sv]; omega_using []
theorem PSizes.o_outO_lt_4096m8 (hz : PSizes H) : H.outO < 4096 * 8 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_olO_mod_8_eq_0 (_hz : PSizes H) : H.olO % 8 = 0 := by
  simp only [Hash.olO, Hash.sv]; omega_using []
theorem PSizes.o_olO_lt_4096m8 (hz : PSizes H) : H.olO < 4096 * 8 := by
  simp only [Hash.olO, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_B_mod_4_eq_0 (hz : PSizes H) : H.P.B % 4 = 0 := by
  have := hz.B4; omega_using [this]
theorem PSizes.o_4mSd4_eq_S (hz : PSizes H) : 4 * (H.S / 4) = H.S := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.N4; omega_arith
theorem PSizes.o_stSO_mod_4_eq_0 (hz : PSizes H) : H.stSO % 4 = 0 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.N4; omega_arith
theorem PSizes.o_stSO_4mSd4_le_4096m4 (hz : PSizes H) : H.stSO + 4 * (H.S / 4) ≤ 4096 * 4 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.B4; have := hz.z.N4; omega_arith
theorem PSizes.o_stWO_mod_4_eq_0 (hz : PSizes H) : H.stWO % 4 = 0 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.N4; omega_arith
theorem PSizes.o_stWO_4mSd4_le_4096m4 (hz : PSizes H) : H.stWO + 4 * (H.S / 4) ≤ 4096 * 4 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.B4; have := hz.z.N4; omega_arith
theorem PSizes.o_intO_mod_4_eq_0 (hz : PSizes H) : H.intO % 4 = 0 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.D4; have := hz.z.N4; omega_arith
theorem PSizes.o_intO_lt_4096m4 (hz : PSizes H) : H.intO < 4096 * 4 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_stWO_le_uO (hz : PSizes H) : H.stWO ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_4mDd4_eq_D (hz : PSizes H) : 4 * (H.D / 4) = H.D := by
  have := hz.z.D4; omega_using [this]
theorem PSizes.o_uO_mod_4_eq_0 (hz : PSizes H) : H.uO % 4 = 0 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.N4; omega_using []
theorem PSizes.o_uO_4mDd4_le_4096m4 (hz : PSizes H) : H.uO + 4 * (H.D / 4) ≤ 4096 * 4 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.B4; have := hz.z.D4; have := hz.z.N4; omega_arith
theorem PSizes.o_tO_mod_4_eq_0 (hz : PSizes H) : H.tO % 4 = 0 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.D4; have := hz.z.N4; omega_arith
theorem PSizes.o_tO_4mDd4_le_4096m4 (hz : PSizes H) : H.tO + 4 * (H.D / 4) ≤ 4096 * 4 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.B4; have := hz.z.D4; have := hz.z.N4; omega_arith
theorem PSizes.o_cO_mod_8_eq_0 (_hz : PSizes H) : H.cO % 8 = 0 := by
  simp only [Hash.cO, Hash.sv]; omega_using []
theorem PSizes.o_cO_lt_4096m8 (hz : PSizes H) : H.cO < 4096 * 8 := by
  simp only [Hash.cO, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_st0O_S_eq_st1O (_hz : PSizes H) : H.st0O + H.S = H.st1O := rfl
theorem PSizes.o_W_le_1024 (hz : PSizes H) : H.W ≤ 1024 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_st0O_le_stWO (hz : PSizes H) : H.st0O ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st0O_le_hkO (hz : PSizes H) : H.st0O ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_D_le_hsF (hz : PSizes H) : H.D ≤ H.stream.F := by
  have := hz.z.DN; have : H.stream.F = H.P.N := rfl; omega_arith
theorem PSizes.o_D_le_B (hz : PSizes H) : H.D ≤ H.P.B := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_st0O_mod_4_eq_0 (_hz : PSizes H) : H.st0O % 4 = 0 := by
  simp only [Hash.st0O, Hash.sv]; omega_using []
theorem PSizes.o_st0O_4mSd4_le_4096m4 (hz : PSizes H) : H.st0O + 4 * (H.S / 4) ≤ 4096 * 4 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.B4; have := hz.z.N4; omega_arith
theorem PSizes.o_B_lt_p16 (hz : PSizes H) : H.P.B < 2 ^ 16 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega_arith
theorem PSizes.o_sv_80_le_stWO (hz : PSizes H) : H.sv + 80 ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_st0O_3mS_le_stWO (hz : PSizes H) : H.st0O + 3 * H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega_using []
theorem PSizes.o_B_5_le_L (hz : PSizes H) : H.P.B + 5 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith
theorem PSizes.o_0_lt_S (hz : PSizes H) : 0 < H.S := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega_arith

end VG.Proof.Pbkdf2.Md.AArch64.Pbk

end

end


/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`, correct

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/PbkLoop.lean`): `pbkdf2` saves our
caller's registers, makes the key (hashing a password longer than a block),
HMAC's states for it and the inner state after the salt.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_addImm wp_subImm wp_movz wp_lsr wp_str eval_zero sub_beq
  toNat_ofNat_lt add_ofNat)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.AArch64 (copy32_ok)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG After SavedRegs SavedRegs.frame save_ok saveR UpdArgs)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep readW_writeW_ne bytesAt_take covers_one)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_getD' writeBytes_at xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

/-! ## Instructions and words -/

theorem wp_subImmW {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth 32 - BitVec.ofNat 32 imm).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .w d n imm :: is)) s Q :=
  VG.Proof.MdStream.AArch64.WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 - BitVec.ofNat 32 imm))
    (by simp [exec, h, State.read]) (k _ (VG.Proof.MdStream.AArch64.Upd.write s .w d _))

/-- `c - 1`, in 32 bits. -/
theorem sub1_32 (x : BitVec 64) (h : 0 < (x.setWidth 32).toNat) :
    (x.setWidth 32 - BitVec.ofNat 32 1).setWidth 64 = BitVec.ofNat 64 ((x.setWidth 32).toNat - 1) := by
  apply BitVec.eq_of_toNat_eq
  have := (x.setWidth 32).isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat] at h this ⊢
  omega_arith

/-- A shift right leaves zero exactly when the value is below the power of two. -/
theorem shr_beq_zero (x : BitVec 64) (k : Nat) : (x >>> k == 0) = decide (x.toNat < 2 ^ k) := by
  obtain hk := Nat.two_pow_pos k
  obtain e : (x >>> k).toNat = x.toNat / 2 ^ k := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases h : x.toNat < 2 ^ k
  · have : x >>> k = 0 := BitVec.eq_of_toNat_eq (by rw [e, Nat.div_eq_of_lt h]; rfl)
    simp [this, h]
  · have hne : (x >>> k == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      obtain h1 : x.toNat / 2 ^ k = 0 := by rw [← e, h0]; rfl
      obtain h2 : 2 ^ k ≤ x.toNat := by omega_arith
      have := Nat.div_le_div_right (c := 2 ^ k) h2
      rw [Nat.div_self hk] at this
      omega_arith
    rw [hne]; simp [h]

theorem log2_B (hz : PSizes H) : 2 ^ Nat.log2 H.P.B = H.P.B ∧ Nat.log2 H.P.B < 64 := by
  rcases hz.z.B with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

/-! ## What the entry sets up, kept until the salt is absorbed -/

/-- The key's registers: `x19` = `password`, `x20` = `password_len`, `x21` =
`salt`, `x22` = `salt_len`. -/
structure KE (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  x19 : s.gpr .x19 = pw s₀
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = salt s₀
  x22 : s.gpr .x22 = s₀.gpr .x3

/-- The registers `KE` fixes. -/
abbrev eregs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

/-- The public ones. -/
abbrev epub : List Reg := [.x19, .x20, .x21, .x22, .x23]

theorem kregs_eregs : ∀ r ∈ kregs, r ∈ eregs := by decide

theorem untouched_ne : ∀ r ∈ untouched, r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x9 ∧ r ≠ .x23 ∧
    r ≠ .x4 ∧ r ≠ .x10 := by decide

theorem KE.upd {s₀ s s' : State} (h : KE (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ eregs) : KE (H := H) s₀ s' := by
  obtain ne : ∀ r ∈ eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u fun h' => hd (kregs_eregs d h'), by rw [u.other _ (ne _ (by simp)), h.x19],
    by rw [u.other _ (ne _ (by simp)), h.x20], by rw [u.other _ (ne _ (by simp)), h.x21],
    by rw [u.other _ (ne _ (by simp)), h.x22]⟩

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem KE.call {s s' : State} (h : KE (H := H) s₀ s) {ws : List Region} (a : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) : KE (H := H) s₀ s' :=
  ⟨h.kr.call hp hz a.rd a.wr a.sp a.cs a.frame hw, by rw [a.cs _ (by simp [preserved]) (by decide), h.x19],
    by rw [a.cs _ (by simp [preserved]) (by decide), h.x20], by rw [a.cs _ (by simp [preserved]) (by decide), h.x21],
    by rw [a.cs _ (by simp [preserved]) (by decide), h.x22]⟩

/-! ## The entry -/

theorem entry_ok : WP isa (.block H.entry) s₀ (KE (H := H) s₀) := by
  have hW := hz.W
  obtain hsnw := hp.snw; have hc0 := hp.c0
  simp only [Hash.entry, Hash.entryPre, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => ?_
  obtain x4 : s₂.gpr .x4 = scr s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  obtain g₂ : ∀ r, r ≠ .x4 → r ≠ .x10 → s₂.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₂.other r h1, u₁.other r h2]
  refine save_ok H.hh (scr := scr s₀) (L := (H.W + H.S) * 8) x4 (by show H.W ≤ 1024; exact hz.o_W_le_1024)
    (by rw [u₂.wr, u₁.wr]; exact sc_mem hp) (by show 8 * H.W + 56 ≤ (H.W + H.S) * 8; exact hz.o_W8_56_le_L)
    fun s₃ g₃ rd₃ wr₃ sp₃ f₃ sv₃ => ?_
  simp only [Hash.entryPost]
  refine wp_mov fun s₄ u₄ => ?_
  obtain x23₄ : s₄.gpr .x23 = scr s₀ := by rw [u₄.gpr, g₃, x4]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, wr₃, u₂.wr, u₁.wr]
  refine wp_str (a := A s₀ H.outO) ⟨by exact hz.o_outO_mod_8_eq_0, by exact hz.o_outO_lt_4096m8⟩ (by rw [x23₄]) (in_sc hp hz wr₄ (by exact hz.o_outO_8_le_L))
    fun s₅ m₅ => ?_
  refine wp_subImmW (by decide) fun s₆ u₆ => ?_
  obtain x23₆ : s₆.gpr .x23 = scr s₀ := by rw [u₆.other _ (by decide), m₅.gpr, x23₄]
  refine wp_str (a := A s₀ H.cO) ⟨by exact hz.o_cO_mod_8_eq_0, by exact hz.o_cO_lt_4096m8⟩ (by rw [x23₆])
    (by rw [u₆.wr, m₅.wr]; exact in_sc hp hz wr₄ (by exact hz.o_cO_8_le_L)) fun s₇ m₇ => ?_
  refine wp_str (a := A s₀ H.olO) ⟨by exact hz.o_olO_mod_8_eq_0, by exact hz.o_olO_lt_4096m8⟩ (by rw [m₇.gpr, x23₆])
    (by rw [m₇.wr, u₆.wr, m₅.wr]; exact in_sc hp hz wr₄ (by exact hz.o_olO_8_le_L)) fun s₈ m₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ => wp_mov fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ =>
    WP.block_nil ?_
  -- The registers.
  obtain g₈ : ∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x4 → r ≠ .x10 → s₈.gpr r = s₀.gpr r := fun r h1 h2 h3 h4 => by
    rw [m₈.gpr, m₇.gpr, u₆.other r h1, m₅.gpr, u₄.other r h2, g₃, g₂ r h3 h4]
  obtain g₁₂ : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → s₁₂.gpr r = s₈.gpr r := fun r a b c d => by
    rw [u₁₂.other r d, u₁₁.other r c, u₁₀.other r b, u₉.other r a]
  obtain v5 : s₄.gpr .x5 = out s₀ := by rw [u₄.other _ (by decide), g₃, g₂ _ (by decide) (by decide)]
  obtain v9 : s₆.gpr .x9 = BitVec.ofNat 64 (cc s₀ - 1) := by
    rw [u₆.gpr, m₅.gpr, u₄.other _ (by decide), g₃, u₂.other _ (by decide), u₁.gpr, sub1_32 _ hc0]
  obtain v6 : s₇.gpr .x6 = s₀.gpr .x6 := by
    rw [m₇.gpr, u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), g₃, g₂ _ (by decide) (by decide)]
  -- The memory.
  obtain m₁₂ : s₁₂.mem = ((s₃.mem.writeW (A s₀ H.outO) (out s₀)).writeW (A s₀ H.cO)
      (BitVec.ofNat 64 (cc s₀ - 1))).writeW (A s₀ H.olO) (s₀.gpr .x6) := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈.mem, v6, m₇.mem, v9, u₆.mem, m₅.mem, v5, u₄.mem]
  obtain d_oc : Region.Disjoint ⟨A s₀ H.outO, 8⟩ ⟨A s₀ H.cO, 8⟩ :=
    part_disj hz (Or.inl (by exact hz.o_outO_8_le_cO)) (by exact hz.o_outO_8_le_L) (by exact hz.o_cO_8_le_L)
  obtain d_ol : Region.Disjoint ⟨A s₀ H.outO, 8⟩ ⟨A s₀ H.olO, 8⟩ :=
    part_disj hz (Or.inl (by exact hz.o_outO_8_le_olO)) (by exact hz.o_outO_8_le_L) (by exact hz.o_olO_8_le_L)
  obtain d_cl : Region.Disjoint ⟨A s₀ H.cO, 8⟩ ⟨A s₀ H.olO, 8⟩ :=
    part_disj hz (Or.inl (by exact hz.o_cO_8_le_olO)) (by exact hz.o_cO_8_le_L) (by exact hz.o_olO_8_le_L)
  obtain fW : Frame [sR s₀ H.outO 24] s₃.mem s₁₂.mem := by
    rw [m₁₂]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl _) (by exact hz.o_outO_64d8_le_outO_24)
      (by exact hz.o_outO_24_lt_p64))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by exact hz.o_outO_le_cO) (by exact hz.o_cO_64d8_le_outO_24) (by exact hz.o_outO_24_lt_p64))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by exact hz.o_outO_le_olO) (by exact hz.o_olO_64d8_le_outO_24) (by exact hz.o_outO_24_lt_p64))
  obtain f₀ : Frame [outR s₀, scR (H := H) s₀, stkR s₀] s₀.mem s₁₂.mem := by
    obtain e₂ : s₂.mem = s₀.mem := by rw [u₂.mem, u₁.mem]
    rw [← e₂]
    refine (f₃.sub fun r hr => ?_).trans (fW.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR (H := H) s₀, by simp, Offset.sub_base _ (by show 8 * H.W + 56 ≤ (H.W + H.S) * 8; exact hz.o_W8_56_le_L)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR (H := H) s₀, by simp, part_sub (by exact hz.o_outO_24_le_L)⟩
  obtain sv : SavedRegs H.hh (scr s₀) s₀ s₃.mem :=
    ⟨by rw [sv₃.x19, g₂ _ (by decide) (by decide)], by rw [sv₃.x20, g₂ _ (by decide) (by decide)],
      by rw [sv₃.x21, g₂ _ (by decide) (by decide)], by rw [sv₃.x22, g₂ _ (by decide) (by decide)],
      by rw [sv₃.x24, g₂ _ (by decide) (by decide)], by rw [sv₃.x30, g₂ _ (by decide) (by decide)],
      by rw [sv₃.x23, g₂ _ (by decide) (by decide)]⟩
  refine ⟨⟨by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, m₈.rd, m₇.rd, u₆.rd, m₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd],
    by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, m₈.wr, m₇.wr, u₆.wr, m₅.wr, wr₄],
    by rw [u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, m₈.sp, m₇.sp, u₆.sp, m₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp],
    by rw [g₁₂ _ (by decide) (by decide) (by decide) (by decide), m₈.gpr, m₇.gpr, x23₆],
    fun r hr => by
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := untouched_ne r hr
      rw [g₁₂ r n1 n2 n3 n4, g₈ r n5 n6 n7 n8],
    SavedRegs.frame H.hh sv fW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (a := 8 * H.W) (m := 56) (Or.inl (by exact hz.o_W8_56_le_outO)) (by exact hz.o_W8_56_le_L) (by exact hz.o_outO_24_le_L),
    by rw [m₁₂, readW_writeW_ne _ _ d_ol, readW_writeW_ne _ _ d_oc, Mem.readW_writeW_self64],
    by rw [m₁₂, readW_writeW_ne _ _ d_cl, Mem.readW_writeW_self64],
    by rw [m₁₂, Mem.readW_writeW_self64], f₀⟩, ?_, ?_, ?_, ?_⟩
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      g₈ _ (by decide) (by decide) (by decide) (by decide)]
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide)]
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide)]
  · rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide)]

end

/-! ## Facts about the hash function -/

theorem _root_.VG.Proof.Pbkdf2.Md.AArch64.HashOK.wb_le (hH : HashOK H) : hH.stream.Wb ≤ 8 * H.W := by
  have := hH.stream.hWb; have e : H.stream.W = (H.P.so + 48) / 8 := rfl; have := hH.sizes.fits; omega_arith

theorem PSizes.o_hsWb_le_L (hz : PSizes H) (hH : HashOK H) : hH.stream.Wb ≤ (H.W + H.S) * 8 := by
  have := hH.wb_le; have := hz.W; omega_arith

theorem hash_len (hH : HashOK H) (m : List Byte) : (hH.SH.H.hash m).length = H.D := by
  rw [hH.hash, List.length_take, VG.Proof.MdStream.Md.hash, hH.md.digest_length]; have := hH.sizes.DN; omega_arith

/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash (hH : HashOK H) {k : List Byte} (hk : H.P.B < k.length) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  obtain hl := hash_len hH k; have hB := hH.hB; have := hH.sizes.pad
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ H.P.B < H.D by omega_arith))]

theorem blockKey_length (hH : HashOK H) (k : List Byte) : (blockKey hH.SH.H k).length = H.P.B := by
  obtain hB := hH.hB; have := hH.sizes.pad
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [hash_len]; omega_arith
  · omega_arith

theorem repr_keep (hH : HashOK H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.stream.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd
    (by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 2 ^ 64; omega_arith) hi) hr

/-- A state copied from `p` to `q` represents the same message. -/
theorem repr_copy (hH : HashOK H) {m : Mem} {p q : Addr} {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr (writeBytes m q (bytesAt m p H.S)) q msg := by
  have : H.S ≤ 256 := by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 256; omega_arith
  refine hH.stream.repr _ _ _ _ _ (fun i hi => ?_) hr
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_arith),
    bytesAt_getD' _ _ (show i < H.S from hi)]

/-! ## Hashing a password longer than a block -/

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp in
theorem hk1_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.hkInit) s fun t => KE (H := H) s₀ t ∧ t.gpr .x0 = A s₀ H.stWO := by
  simp only [Hash.hkInit]
  exact wp_addImm (by exact hz.o_stWO_lt_4096) fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), by rw [u₁.gpr, h.kr.x23]⟩

theorem hk2_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hx0 : s.gpr .x0 = A s₀ H.stWO) :
    WP isa (.call H.initN H.initC) s fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  exact VG.Proof.Pbkdf2.Md.AArch64.Calls.init_call hH.stream (st := A s₀ H.stWO) hx0
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by exact hz.o_stWO_hsS_le_L))
    fun s₂ a₂ r₂ => ⟨h.call hp hz a₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩, r₂⟩

/-- `update`'s arguments: the password. -/
theorem hk3_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.block H.hkUpd) s fun t => KE (H := H) s₀ t ∧
      UpdArgs hH.stream t (A s₀ H.stWO) (pw s₀) (scr s₀) (pwl s₀) ∧
      t.gpr .x1 = BitVec.ofNat 64 0 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  simp only [Hash.hkUpd]
  refine wp_addImm (by exact hz.o_stWO_lt_4096) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => WP.block_nil ?_
  obtain k₅ := ((((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)).upd u₅
    (by decide)
  refine ⟨k₅, ?_, by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hr⟩
  exact
    { x0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x2 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h.x19]
      x3 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.x20]
      x4 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.kr.x23]
      cd := covers_one (List.mem_append_left _ (by rw [k₅.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₅.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_low hp k₅.kr (by exact hz.o_hsWb_le_L hH)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix hWb)
      d_st := hp.pw_s.sub_right (part_sub (by exact hz.o_stWO_hsS_le_L))
      d_sc := hp.pw_s.sub_right (Region.sub_prefix (by exact hz.o_hsWb_le_L hH))
      sp16 := by rw [k₅.kr.sp]; exact hp.sp16
      stk_st := stk_sc hp k₅.kr (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_d := by rw [k₅.kr.sp]; exact hp.stk_pw
      stk_sc := stk_sc hp k₅.kr (Region.sub_prefix (by exact hz.o_hsWb_le_L hH)) }

theorem hk4_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (ua : UpdArgs hH.stream s (A s₀ H.stWO) (pw s₀) (scr s₀) (pwl s₀))
    (hx1 : s.gpr .x1 = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.call H.updN H.updC) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_call hH.stream ua fun s₈ a₈ r₈ =>
    ⟨h.call hp hz a₈ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · have := r₈ [] hr hx1
    rwa [List.nil_append, h.kr.pwBytes hp] at this

/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.block H.hkFin) s fun t => KE (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH.stream t (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀) ∧
      t.gpr .x1 = s₀.gpr .x1 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hF : H.stream.F = H.P.N := rfl
  simp only [Hash.hkFin]
  refine wp_addImm (by exact hz.o_stWO_lt_4096) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_addImm (by exact hz.o_hkO_lt_4096) fun s₃ u₃ =>
    wp_mov fun s₄ u₄ => WP.block_nil ?_
  obtain k₄ := (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  refine ⟨k₄, ?_, by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x20],
    by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hr⟩
  exact
    { x0 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x2 := by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      x3 := by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₄.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_part hp k₄.kr (by exact hz.o_hkO_hsF_le_L)
        · exact cov_low hp k₄.kr (by exact hz.o_hsWb_le_L hH)
      st_o := part_disj hz (Or.inl (by exact hz.o_stWO_hsS_le_hkO)) (by exact hz.o_stWO_hsS_le_L) (by exact hz.o_hkO_hsF_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix hWb)
      o_sc := (low_disj hz (by exact hz.o_W8_le_hkO) (by exact hz.o_hkO_hsF_le_L)).sub_right (Region.sub_prefix hWb)
      sp16 := by rw [k₄.kr.sp]; exact hp.sp16
      stk_st := stk_sc hp k₄.kr (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_o := stk_sc hp k₄.kr (part_sub (by exact hz.o_hkO_hsF_le_L))
      stk_sc := stk_sc hp k₄.kr (Region.sub_prefix (by exact hz.o_hsWb_le_L hH)) }

theorem hk6_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (fa : VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH.stream s (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀))
    (hx1 : s.gpr .x1 = s₀.gpr .x1) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.call H.finN H.finC) s fun t => KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  obtain hWb := hH.wb_le; have hD := hz.z.DN
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.fin_call hH.stream fa fun s₁₃ a₁₃ r₁₃ =>
    ⟨h.call hp hz a₁₃ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_hkO, by exact hz.o_hkO_hsF_le_L⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · rw [bytesAt_take _ _ (show H.D ≤ H.stream.F by exact hz.o_D_le_hsF)]
    exact r₁₃ _ hr (by rw [bytesAt_length]; exact (s₀.gpr .x1).isLt)
      (by rw [hx1, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp in
theorem hk7_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.hkKey) s fun t =>
      KE (H := H) s₀ t ∧ t.gpr .x2 = A s₀ H.hkO ∧ (t.gpr .x3).toNat = H.D ∧ t.mem = s.mem := by
  obtain hD := hz.z.DN; have hN := hz.N
  simp only [Hash.hkKey]
  refine wp_addImm (by exact hz.o_hkO_lt_4096) fun s₁ u₁ => wp_movz fun s₂ u₂ => WP.block_nil ?_
  exact ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.kr.x23],
    by rw [u₂.gpr, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show H.D < 2 ^ 16 by exact hz.o_D_lt_p16), Nat.mod_eq_of_lt (show H.D < 2 ^ 64 by exact hz.o_D_lt_p64)],
    by rw [u₂.mem, u₁.mem]⟩

theorem hashKey_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) :
    WP isa H.hashKey s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = A s₀ H.hkO ∧ (t.gpr .x3).toNat = H.D ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (hk1_ok hz h) fun s₁ ⟨k₁, d₁⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hp hz hH k₂ r₂) fun s₃ ⟨k₃, a₃, i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok hp hz hH k₄ r₄) fun s₅ ⟨k₅, a₅, i₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok hz k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

end

/-! ## The key -/

/-- Where the key is, and its length. -/
abbrev kp (H : Hash) (s₀ : State) : Addr := if pwl s₀ < H.P.B + 1 then pw s₀ else A s₀ H.hkO
abbrev kl (H : Hash) (s₀ : State) : Nat := if pwl s₀ < H.P.B + 1 then pwl s₀ else H.D

/-- The key HMAC's `init` gets: the password, or the digest of a password
longer than a block, in `scratch`; either gives the same `K₀`. -/
structure KeyAt (hH : HashOK H) (s₀ : State) (m : Mem) (kp : Addr) (kl : Nat) : Prop where
  loc : (kp = pw s₀ ∧ kl = pwl s₀) ∨ (kp = A s₀ H.hkO ∧ kl = H.D)
  le : kl ≤ H.P.B
  k0 : blockKey hH.SH.H (bytesAt m kp kl) = blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- `K₀`, the password as a key. -/
abbrev K0 (hH : HashOK H) (s₀ : State) : List Byte := blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- HMAC's states in `scratch`: `K₀ ⊕ ipad`, `K₀ ⊕ opad`, and `K₀ ⊕ ipad`
after the salt. -/
structure States (hH : HashOK H) (s₀ : State) (m : Mem) : Prop where
  i : hH.SH.Repr m (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad)
  o : hH.SH.Repr m (A s₀ H.st1O) (xorPad (K0 hH s₀) opad)
  s : hH.SH.Repr m (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad ++ bytesAt s₀.mem (salt s₀) (sl s₀))

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hz in
theorem short_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hs : pwl s₀ < H.P.B + 1) :
    WP isa (.block Hash.short) s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = kp H s₀ ∧
      (t.gpr .x3).toNat = kl H s₀ ∧ KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  obtain e₁ : kp H s₀ = pw s₀ := ite_eq_left_of_eq_true _ _ (eq_true hs)
  obtain e₂ : kl H s₀ = pwl s₀ := ite_eq_left_of_eq_true _ _ (eq_true hs)
  rw [e₁, e₂]
  simp only [Hash.short]
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => WP.block_nil ?_
  refine ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.x19],
    by rw [u₂.gpr, u₁.other _ (by decide), h.x20], ⟨.inl ⟨rfl, rfl⟩, by omega_arith, ?_⟩⟩
  rw [u₂.mem, u₁.mem, h.kr.pwBytes hp]

theorem long_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hs : ¬ pwl s₀ < H.P.B + 1) :
    WP isa H.hashKey s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = kp H s₀ ∧
      (t.gpr .x3).toNat = kl H s₀ ∧ KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  obtain hD := hz.z.DN; have := hz.z.pad
  obtain e₁ : kp H s₀ = A s₀ H.hkO := ite_eq_right_of_eq_false _ _ (eq_false hs)
  obtain e₂ : kl H s₀ = H.D := ite_eq_right_of_eq_false _ _ (eq_false hs)
  rw [e₁, e₂]
  refine WP.mono (hashKey_ok hp hz hH h) fun t ⟨k, x2, x3, hb⟩ =>
    ⟨k, x2, x3, ⟨.inr ⟨rfl, rfl⟩, by exact hz.o_D_le_B, ?_⟩⟩
  rw [hb, blockKey_hash hH (by rw [bytesAt_length]; omega_arith)]

omit hp in
/-- The value of `x9` the key's first branch tests. -/
theorem key_shr {s : State} (h : KE (H := H) s₀ s) {s₁ : State}
    (u : Upd s s₁ .x9 (s.gpr .x20 >>> Nat.log2 H.P.B)) :
    isa.eval (.zero .x .x9) s₁ = some (decide (pwl s₀ < H.P.B)) := by
  change eval (.zero .x .x9) s₁ = _
  rw [eval_zero, u.gpr, h.x20, shr_beq_zero, (log2_B hz).1]

omit hp hz in
/-- The value of `x9` the key's second branch tests. -/
theorem key_sub {s : State} (h : KE (H := H) s₀ s) {s₂ : State}
    (u : Upd s s₂ .x9 (s.gpr .x20 - BitVec.ofNat 64 H.P.B)) (hB : H.P.B < 2 ^ 64) :
    isa.eval (.zero .x .x9) s₂ = some (decide (pwl s₀ = H.P.B)) := by
  change eval (.zero .x .x9) s₂ = _
  obtain ex : s₀.gpr .x1 = BitVec.ofNat 64 (pwl s₀) := by simp
  rw [eval_zero, u.gpr, h.x20, ex, sub_beq (s₀.gpr .x1).isLt hB]

theorem key_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) :
    WP isa H.key s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = kp H s₀ ∧ (t.gpr .x3).toNat = kl H s₀ ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hB := hz.B_le
  unfold Hash.key Hash.keyShr Hash.keySub
  refine WP.seq (wp_lsr (log2_B hz).2 fun s₁ u₁ => WP.block_nil ?_)
  obtain k₁ := h.upd u₁ (by decide)
  refine WP.ite _ (key_shr hz h u₁) (fun hT => short_ok hp hH k₁ (by have := of_decide_eq_true hT; omega_arith))
    fun hF => ?_
  refine WP.seq (wp_subImm (by exact hz.o_B_lt_4096) fun s₂ u₂ => WP.block_nil ?_)
  obtain k₂ := k₁.upd u₂ (by decide)
  refine WP.ite _ (key_sub k₁ u₂ (by exact hz.o_B_lt_p64)) (fun hT => short_ok hp hH k₂ (by
    have := of_decide_eq_true hT; omega_arith)) fun hF' => long_ok hp hz hH k₂ (by
      have := of_decide_eq_false hF; have := of_decide_eq_false hF'; omega_arith)

/-! ## HMAC's states -/

omit hp in
theorem States.keep (hH : HashOK H) {m m' : Mem} (h : States hH s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ H.st0O (3 * H.S)) r) : States hH s₀ m' := by
  exact ⟨repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by exact hz.o_st0O_S_le_st0O_3mS))) h.i,
    repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by exact hz.o_st0O_le_st1O) (by exact hz.o_st1O_S_le_st0O_3mS))) h.o,
    repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by exact hz.o_st0O_le_stSO) (by exact hz.o_stSO_S_le_st0O_3mS))) h.s⟩

/-- The key's region: where HMAC's `init` may read it. -/
theorem KeyAt.facts (hH : HashOK H) {m : Mem} {kp : Addr} {kl : Nat} (hk : KeyAt hH s₀ m kp kl) {s : State}
    (h : KR (H := H) s₀ s) :
    Covers [⟨kp, kl⟩] (s.rd ++ s.wr) ∧ Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st0O, H.S⟩ ∧
      Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st1O, H.S⟩ ∧ Region.Disjoint ⟨kp, kl⟩ (lowR (H := H) s₀) ∧
      (below s.sp 16).Disjoint ⟨kp, kl⟩ := by
  obtain hD := hz.z.DN; have hN := hz.N
  rcases hk.loc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨covers_one (List.mem_append_left _ (by rw [h.rd, hp.rd]; simp)),
      hp.pw_s.sub_right (part_sub (by exact hz.o_st0O_S_le_L)), hp.pw_s.sub_right (part_sub (by exact hz.o_st1O_S_le_L)),
      hp.pw_s.sub_right low_sub, by rw [h.sp]; exact hp.stk_pw⟩
  · refine ⟨Covers.of_sub fun r hr => ?_, part_disj hz (Or.inr (by exact hz.o_st0O_S_le_hkO)) (by exact hz.o_hkO_D_le_L) (by exact hz.o_st0O_S_le_L),
      part_disj hz (Or.inr (by exact hz.o_st1O_S_le_hkO)) (by exact hz.o_hkO_D_le_L) (by exact hz.o_st1O_S_le_L), low_disj hz (by exact hz.o_W8_le_hkO) (by exact hz.o_hkO_D_le_L),
      stk_sc hp h (part_sub (by exact hz.o_hkO_D_le_L))⟩
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨r', h', off, e, l⟩ := cov_part hp h (o := H.hkO) (n := H.D) (by exact hz.o_hkO_D_le_L)
    exact ⟨r', List.mem_append_right _ h', off, e, l⟩

/-- HMAC's `init`'s arguments: its two states and the key. -/
theorem su1_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hx2 : s.gpr .x2 = kp H s₀)
    (hx3 : (s.gpr .x3).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.block H.initArgs) s fun t => KE (H := H) s₀ t ∧
      InitArgs (H := H) t (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀) ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  obtain hL := L_lt hz
  have hsnw := hp.snw
  simp only [Hash.initArgs]
  refine wp_addImm (by exact hz.o_st0O_lt_4096) fun s₁ u₁ => wp_addImm (by exact hz.o_st1O_lt_4096) fun s₂ u₂ => wp_mov fun s₃ u₃ =>
    WP.block_nil ?_
  obtain k₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain ⟨kc, k_i, k_o, k_s, k_stk⟩ := hk.facts hp hz hH k₃.kr
  refine ⟨k₃, ?_, m₃ ▸ hk⟩
  exact
    { x0 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x1 := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.kr.x23]
      x2 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx2]
      x3 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx3]
      x4 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      klB := hk.le
      cr := kc
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₃.kr (by exact hz.o_st0O_S_le_L)
        · exact cov_part hp k₃.kr (by exact hz.o_st1O_S_le_L)
        · exact cov_low hp k₃.kr (by exact hz.o_W8_le_L)
      i_o := part_disj hz (Or.inl (by exact hz.o_st0O_S_le_st1O)) (by exact hz.o_st0O_S_le_L) (by exact hz.o_st1O_S_le_L)
      i_s := low_disj hz (by exact hz.o_W8_le_st0O) (by exact hz.o_st0O_S_le_L)
      o_s := low_disj hz (by exact hz.o_W8_le_st1O) (by exact hz.o_st1O_S_le_L)
      k_i := k_i
      k_o := k_o
      k_s := k_s
      sp16 := by rw [k₃.kr.sp]; exact hp.sp16
      stk_i := stk_sc hp k₃.kr (part_sub (by exact hz.o_st0O_S_le_L))
      stk_o := stk_sc hp k₃.kr (part_sub (by exact hz.o_st1O_S_le_L))
      stk_k := k_stk
      stk_s := stk_sc hp k₃.kr low_sub
      scnw := by show (scr s₀).toNat + 8 * H.W ≤ 2 ^ 64; omega_arith }

/-- HMAC's `init`: the key's inner and outer states. -/
theorem su2_ok (hH : HashOK H) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.aarch64Depth ≤ 1) {s : State} (h : KE (H := H) s₀ s)
    (ia : InitArgs (H := H) s (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀))
    (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.call H.hmacInitN H.hmacInit) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad) := by
  refine hinit_call hH hI hId ia fun s₄ a₄ ri₄ ro₄ => ⟨?_, ?_, ?_⟩
  · exact h.call hp hz a₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_st0O_S_le_L⟩
      · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_st1O, by exact hz.o_st1O_S_le_L⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · rw [hk.k0] at ri₄; exact ri₄
  · rw [hk.k0] at ro₄; exact ro₄

/-- The inner state copied, and `update`'s arguments: the salt. -/
theorem su3_ok (hH : HashOK H) {s₄ : State} (h : KE (H := H) s₀ s₄)
    (ri₄ : hH.SH.Repr s₄.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad))
    (ro₄ : hH.SH.Repr s₄.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad)) :
    WP isa (.block H.saltArgs) s₄ fun t => KE (H := H) s₀ t ∧
      UpdArgs hH.stream t (A s₀ H.stSO) (salt s₀) (scr s₀) (sl s₀) ∧
      t.gpr .x1 = BitVec.ofNat 64 H.P.B ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad) ∧
      hH.SH.Repr t.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad) := by
  have hWb := hH.wb_le
  obtain hB := hz.B_le; have hN4 := hz.z.N4
  obtain hB4 : H.P.B % 4 = 0 := by rcases hz.z.B with h | h <;> exact hz.o_B_mod_4_eq_0
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  obtain eS : 4 * (H.S / 4) = H.S := by exact hz.o_4mSd4_eq_S
  simp only [Hash.saltArgs, Hash.copy32]
  refine copy32_ok (src := .x23) (dst := .x23) (by decide) (by decide) H.st0O H.stSO (H.S / 4)
    ⟨by exact hz.o_st0O_mod_4_eq_0, by exact hz.o_st0O_4mSd4_le_4096m4⟩ ⟨by exact hz.o_stSO_mod_4_eq_0, by exact hz.o_stSO_4mSd4_le_4096m4⟩ _ s₄ _
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_rw hp hz h.kr (by omega_using [hj, hz.o_st0O_S_le_L]))
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_stSO_S_le_L]))
    (by rw [h.kr.x23, eS]; exact (part_disj hz (Or.inl (by exact hz.o_st0O_S_le_stSO)) (by exact hz.o_st0O_S_le_L) (by exact hz.o_stSO_S_le_L)).sep
          (Region.contains_self _ _) (Region.contains_self _ _))
    fun s₅ g₅ rd₅ wr₅ sp₅ m₅ => ?_
  rw [h.kr.x23, eS] at m₅
  obtain f₅ : Frame [sR s₀ H.stSO H.S] s₄.mem s₅.mem := by
    rw [m₅]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain g : ∀ r ∈ eregs, s₅.gpr r = s₄.gpr r := fun r hr => g₅ r (by rintro rfl; revert hr; decide)
  obtain k₅ : KE (H := H) s₀ s₅ := ⟨h.kr.write hz rd₅ wr₅ sp₅ (fun r hr => g r (kregs_eregs r hr))
      (o := H.stSO) (n := H.S) (by exact hz.o_st0O_le_stSO) (by exact hz.o_stSO_S_le_L) f₅,
    by rw [g _ (by simp), h.x19], by rw [g _ (by simp), h.x20], by rw [g _ (by simp), h.x21],
    by rw [g _ (by simp), h.x22]⟩
  obtain dS : ∀ o, o + H.S ≤ H.stSO → ∀ r ∈ [sR s₀ H.stSO H.S], Region.Disjoint ⟨A s₀ o, H.S⟩ r :=
    fun o ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl ho) (by omega_using [ho, hz.o_stSO_S_le_L]) (by exact hz.o_stSO_S_le_L)
  obtain ri₅ := repr_keep hH f₅ (dS _ (by exact hz.o_st0O_S_le_stSO)) ri₄
  obtain ro₅ := repr_keep hH f₅ (dS _ (by exact hz.o_st1O_S_le_stSO)) ro₄
  obtain rs₅ : hH.SH.Repr s₅.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad) := by rw [m₅]; exact repr_copy hH ri₄
  refine wp_addImm (by exact hz.o_stSO_lt_4096) fun s₆ u₆ => wp_movz fun s₇ u₇ => wp_mov fun s₈ u₈ =>
    wp_mov fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ => WP.block_nil ?_
  obtain k₁₀ := ((((k₅.upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀
    (by decide)
  obtain m₁₀ : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  refine ⟨k₁₀, ?_, ?_, m₁₀ ▸ ri₅, m₁₀ ▸ ro₅, m₁₀ ▸ rs₅⟩
  · exact
      { x0 := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
            u₇.other _ (by decide), u₆.gpr, k₅.kr.x23]
        x2 := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
            u₆.other _ (by decide), k₅.x21]
        x3 := by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
            u₆.other _ (by decide), k₅.x22]
        x4 := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
            u₆.other _ (by decide), k₅.kr.x23]
        cd := covers_one (List.mem_append_left _ (by rw [k₁₀.kr.rd, hp.rd]; simp))
        cw := Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp k₁₀.kr (by exact hz.o_stSO_hsS_le_L)
          · exact cov_low hp k₁₀.kr (by exact hz.o_hsWb_le_L hH)
        st_sc := (low_disj hz (by exact hz.o_W8_le_stSO) (by exact hz.o_stSO_hsS_le_L)).sub_right (Region.sub_prefix hWb)
        d_st := hp.sa_s.sub_right (part_sub (by exact hz.o_stSO_hsS_le_L))
        d_sc := hp.sa_s.sub_right (Region.sub_prefix (by exact hz.o_hsWb_le_L hH))
        sp16 := by rw [k₁₀.kr.sp]; exact hp.sp16
        stk_st := stk_sc hp k₁₀.kr (part_sub (by exact hz.o_stSO_hsS_le_L))
        stk_d := by rw [k₁₀.kr.sp]; exact hp.stk_sa
        stk_sc := stk_sc hp k₁₀.kr (Region.sub_prefix (by exact hz.o_hsWb_le_L hH)) }
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show H.P.B < 2 ^ 16 by exact hz.o_B_lt_p16), Nat.mod_eq_of_lt (show H.P.B < 2 ^ 64 by exact hz.o_B_lt_p64)]

/-- `update` with the salt. -/
theorem su4_ok (hH : HashOK H) {s₁₀ : State} (k₁₀ : KE (H := H) s₀ s₁₀)
    (ua : UpdArgs hH.stream s₁₀ (A s₀ H.stSO) (salt s₀) (scr s₀) (sl s₀))
    (hx1 : s₁₀.gpr .x1 = BitVec.ofNat 64 H.P.B)
    (ri : hH.SH.Repr s₁₀.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad))
    (ro : hH.SH.Repr s₁₀.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad))
    (rs : hH.SH.Repr s₁₀.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad)) :
    WP isa (.call H.updN H.updC) s₁₀ fun t => KE (H := H) s₀ t ∧ States hH s₀ t.mem := by
  have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_call hH.stream ua fun s₁₁ a₁₁ r₁₁ => ?_
  obtain k₁₁ := k₁₀.call hp hz a₁₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stSO, by exact hz.o_stSO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, hWb⟩
  obtain dW : ∀ o, H.st0O ≤ o → o + H.S ≤ H.stSO → ∀ r ∈ [(⟨A s₀ H.stSO, H.stream.S⟩ : Region),
      ⟨scr s₀, hH.stream.Wb⟩] ++ [below s₁₀.sp 16], Region.Disjoint ⟨A s₀ o, H.S⟩ r := fun o ho₀ ho r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact part_disj hz (Or.inl ho) (by omega_using [ho, hz.o_stSO_S_le_L]) (by exact hz.o_stSO_hsS_le_L)
      · exact (low_disj hz (by omega_using [ho₀, hz.o_W8_le_st0O]) (by omega_using [ho, hz.o_stSO_S_le_L])).sub_right (Region.sub_prefix hWb)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (stk_sc hp k₁₀.kr (part_sub (by omega_using [ho, hz.o_stSO_S_le_L]))).symm
  refine ⟨k₁₁, ⟨repr_keep hH a₁₁.frame (dW _ (by exact hz.o_st0O_le_st0O) (by exact hz.o_st0O_S_le_stSO)) ri,
    repr_keep hH a₁₁.frame (dW _ (by exact hz.o_st0O_le_st1O) (by exact hz.o_st1O_S_le_stSO)) ro, ?_⟩⟩
  have := r₁₁ _ rs (by rw [hx1, xorPad_length, blockKey_length])
  rwa [k₁₀.kr.saltBytes hp] at this

theorem setup_ok (hH : HashOK H) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.aarch64Depth ≤ 1) {s : State} (h : KE (H := H) s₀ s)
    (hx2 : s.gpr .x2 = kp H s₀) (hx3 : (s.gpr .x3).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa H.setup s fun t => KE (H := H) s₀ t ∧ States hH s₀ t.mem := by
  unfold Hash.setup
  refine WP.seq (WP.mono (su1_ok hp hz hH h hx2 hx3 hk) fun s₁ ⟨k₁, a₁, h₁⟩ => ?_)
  refine WP.seq (WP.mono (su2_ok hp hz hH hI hId k₁ a₁ h₁) fun s₂ ⟨k₂, i₂, o₂⟩ => ?_)
  refine WP.seq (WP.mono (su3_ok hp hz hH k₂ i₂ o₂) fun s₃ ⟨k₃, a₃, x₃, i₃, o₃, r₃⟩ => ?_)
  exact su4_ok hp hz hH k₃ a₃ x₃ i₃ o₃ r₃

end

end VG.Proof.Pbkdf2.Md.AArch64.Pbk

end

end

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`'s loop

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/PbkLoop.lean`): after `k` blocks of the
output (`Inv`), `out` holds the first `min (k D) out_len` bytes of `T₁ ‖ … ‖
T_k`; a step computes `T_{k+1}` (`U₁` by `update` with `INT (k + 1)` and
HMAC's `finalize`, then `iterate`) and copies as much of it as the output
still needs.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_addImm wp_subImm wp_movz wp_lsr wp_ldr wp_str32 wp_ldrb
  wp_strb wp_add wp_sub wp_rev32 eval_zero eval_nonzero sub_ofNat add_ofNat ofNat_succ ofNat_beq_zero writeW32
  setWidth32)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK pbkG)
open VG.Proof.Pbkdf2.AArch64 (copy32_ok iterK)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG After UpdArgs restore_ok savedRegs CopyInv clob nm count_loop
  movz_ofNat ofNat_ne_zero)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take bytesAt_snoc' writeBytes_snoc not_mem_of_disjoint
  bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

/-! ## The specification's pieces -/

/-- The pseudorandom function: HMAC keyed with the password. -/
abbrev prf (hH : HashOK H) (s₀ : State) : List Byte → List Byte := hmacBlockKey hH.SH.H (K0 hH s₀)

abbrev saltB (s₀ : State) : List Byte := bytesAt s₀.mem (salt s₀) (sl s₀)

/-- `T_i`. -/
abbrev Tb (hH : HashOK H) (s₀ : State) (i : Nat) : List Byte := Spec.Pbkdf2.F (prf hH s₀) (saltB s₀) (cc s₀) i

/-- `T₁ ‖ … ‖ T_k`. -/
def G (hH : HashOK H) (s₀ : State) (k : Nat) : List Byte := (List.range k).flatMap fun j => Tb hH s₀ (j + 1)

theorem G_succ (hH : HashOK H) (s₀ : State) (k : Nat) : G hH s₀ (k + 1) = G hH s₀ k ++ Tb hH s₀ (k + 1) := by
  simp only [G, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The number of blocks of the output. -/
abbrev nb (H : Hash) (s₀ : State) : Nat := (ol s₀ + H.D - 1) / H.D

/-- The bytes of the output after `k` blocks. -/
abbrev done (H : Hash) (s₀ : State) (k : Nat) : Nat := min (k * H.D) (ol s₀)

theorem lt_nb {s₀ : State} (hD : 0 < H.D) {k : Nat} : k < nb H s₀ ↔ k * H.D < ol s₀ := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hD, Nat.succ_mul]; omega_using [hD]

theorem ol_le {s₀ : State} (hD : 0 < H.D) : ol s₀ ≤ nb H s₀ * H.D := by
  obtain h1 : nb H s₀ * H.D + (ol s₀ + H.D - 1) % H.D = ol s₀ + H.D - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  obtain h2 := Nat.mod_lt (ol s₀ + H.D - 1) hD
  omega_using [h1, h2]

theorem nb_lt {s₀ : State} (hD : 0 < H.D) (h : ol s₀ ≤ (2 ^ 32 - 1) * H.D) : nb H s₀ < 2 ^ 32 := by
  rw [Nat.div_lt_iff_lt_mul hD]; omega_using [hD, h]

theorem nb_zero {s₀ : State} (hD : 0 < H.D) : nb H s₀ = 0 ↔ ol s₀ = 0 := by
  have := lt_nb (s₀ := s₀) hD (k := 0); simp only [Nat.zero_mul] at this; omega_using [this]

/-! ## Facts about words, lengths and registers -/

theorem bytes32_int (i : Nat) : VG.Proof.MdStream.bytes32 true (BitVec.ofNat 32 i) = Spec.Pbkdf2.int i := by
  simp only [VG.Proof.MdStream.bytes32, ite_true, Spec.Pbkdf2.int, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  · exact Memory.mod32_div_mod8 i 24 (by decide)
  · exact Memory.mod32_div_mod8 i 16 (by decide)
  · exact Memory.mod32_div_mod8 i 8 (by decide)
  · rw [Nat.pow_zero, Nat.div_one]; exact Nat.mod_mod_of_dvd _ (by decide)

/-- Two disjoint regions that do not wrap around fit in the address space
together. -/
theorem len_add_le {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) (h₁ : r₁.base.toNat + r₁.len ≤ 2 ^ 64)
    (h₂ : r₂.base.toNat + r₂.len ≤ 2 ^ 64) : r₁.len + r₂.len ≤ 2 ^ 64 := by
  by_contra hc
  rcases Nat.le_total r₁.base.toNat r₂.base.toNat with hb | hb
  · refine hd r₂.base ?_ ?_ <;> simp only [Region.Contains]
    · rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hb)]; omega_using [h₂, hc]
    · simp only [BitVec.sub_self, BitVec.toNat_zero]; omega_using [h₁, hc]
  · refine hd r₁.base ?_ ?_ <;> simp only [Region.Contains]
    · simp only [BitVec.sub_self, BitVec.toNat_zero]; omega_using [h₂, hc]
    · rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hb)]; omega_using [h₁, hc]

theorem eregs_pres : ∀ r ∈ eregs, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem eregs_clob : ∀ r ∈ eregs, r ∉ clob := by decide

theorem kregs_clob : ∀ r ∈ kregs, r ∉ clob := by decide

/-- A do-while loop on `x21 ≠ 0` whose body runs `n > 0` times. -/
theorem nb_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s → WP isa body s fun s' => I (k + 1) s' ∧
      isa.eval (.nonzero .x .x21) s' = some (decide (k + 1 ≠ n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x .x21)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_using [], hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hl], hi'⟩

/-! ## The loop's invariant -/

/-- After `k` blocks of the output: `x19` is the next block's number, `x20`
`salt_len`, `x21` the bytes left and `x22` where they go. -/
structure Inv (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR (H := H) s₀ s
  st : States hH s₀ s.mem
  x19 : s.gpr .x19 = BitVec.ofNat 64 (k + 1)
  x20 : s.gpr .x20 = s₀.gpr .x3
  x21 : s.gpr .x21 = BitVec.ofNat 64 (ol s₀ - done H s₀ k)
  x22 : s.gpr .x22 = out s₀ + BitVec.ofNat 64 (done H s₀ k)
  glen : (G hH s₀ k).length = k * H.D
  outB : bytesAt s.mem (out s₀) (done H s₀ k) = (G hH s₀ k).take (done H s₀ k)

/-- In step `k`, before `T_{k+1}` is copied out. -/
structure Mid (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR (H := H) s₀ s
  st : States hH s₀ s.mem
  x19 : s.gpr .x19 = BitVec.ofNat 64 (k + 1)
  x20 : s.gpr .x20 = s₀.gpr .x3
  x21 : s.gpr .x21 = BitVec.ofNat 64 (ol s₀ - k * H.D)
  x22 : s.gpr .x22 = out s₀ + BitVec.ofNat 64 (k * H.D)
  outB : bytesAt s.mem (out s₀) (k * H.D) = G hH s₀ k

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem loopRegs_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hS : States hH s₀ s.mem) :
    WP isa (.block H.loopRegs) s fun t =>
      Inv hH s₀ 0 t ∧ isa.eval (.zero .x .x21) t = some (decide (ol s₀ = 0)) := by
  simp only [Hash.loopRegs]
  refine wp_mov fun s₁ u₁ => ?_
  obtain k₁ := h.kr.upd u₁ (by decide)
  refine wp_ldr (a := A s₀ H.outO) ⟨by exact hz.o_outO_mod_8_eq_0, by exact hz.o_outO_lt_4096m8⟩ (by rw [k₁.x23]) (in_rw hp hz k₁ (by exact hz.o_outO_8_le_L))
    fun s₂ u₂ => ?_
  obtain k₂ := k₁.upd u₂ (by decide)
  refine wp_ldr (a := A s₀ H.olO) ⟨by exact hz.o_olO_mod_8_eq_0, by exact hz.o_olO_lt_4096m8⟩ (by rw [k₂.x23]) (in_rw hp hz k₂ (by exact hz.o_olO_8_le_L))
    fun s₃ u₃ => ?_
  obtain k₃ := k₂.upd u₃ (by decide)
  refine wp_movz fun s₄ u₄ => WP.block_nil ?_
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain x21 : s₄.gpr .x21 = BitVec.ofNat 64 (ol s₀) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, h.kr.olW, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨⟨k₃.upd u₄ (by decide), m₄ ▸ hS, by rw [u₄.gpr]; rfl, ?_, ?_, ?_, by simp [G], by simp [bytesAt]⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x22]
  · rw [x21]; simp
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, h.kr.outW]; simp
  · change eval (.zero .x .x21) s₄ = _
    rw [eval_zero, x21, ofNat_beq_zero (s₀.gpr .x6).isLt]

/-- What writes leave: they are in the working space of the functions we
call, in `scratch` from the working state on, or the 16 bytes below the
stack pointer. -/
theorem Mid.keep (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hg : ∀ r ∈ eregs, s'.gpr r = s.gpr r)
    {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, (∃ j, r = ⟨scr s₀, j⟩ ∧ j ≤ 8 * H.W) ∨
      (∃ o j, r = sR s₀ o j ∧ H.stWO ≤ o ∧ o + j ≤ (H.W + H.S) * 8) ∨ r = below s.sp 16) :
    Mid hH s₀ k s' := by
  obtain ho : Region.Sub ⟨out s₀, k * H.D⟩ (outR s₀) := Region.sub_prefix hk
  obtain key : ∀ {X : Region}, (∀ o j, H.stWO ≤ o → o + j ≤ (H.W + H.S) * 8 → X.Disjoint (sR s₀ o j)) →
      X.Disjoint (lowR (H := H) s₀) → X.Disjoint (below s.sp 16) → ∀ r ∈ rs, X.Disjoint r := by
    intro X h1 h2 h3 r hr
    rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, ho1, ho2⟩ | rfl
    · exact h2.sub_right (Region.sub_prefix hj)
    · exact h1 o j ho1 ho2
    · exact h3
  obtain hstk : ∀ {X : Region}, Region.Sub X (scR (H := H) s₀) → X.Disjoint (below s.sp 16) :=
    fun hX => (stk_sc hp h.kr hX).symm
  refine ⟨h.kr.keep hrd hwr hsp (fun r hr => hg r (kregs_eregs r hr)) hf
      (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega_using [h1, hz.o_sv_80_le_stWO])) (by exact hz.o_sv_80_le_L) h2) (low_disj hz (by exact hz.o_W8_le_sv) (by exact hz.o_sv_80_le_L))
        (hstk (part_sub (by exact hz.o_sv_80_le_L)))) (fun r hr => ?_),
    h.st.keep hz hH hf (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega_using [h1, hz.o_st0O_3mS_le_stWO])) (by exact hz.o_st0O_3mS_le_L) h2)
      (low_disj hz (by exact hz.o_W8_le_st0O) (by exact hz.o_st0O_3mS_le_L)) (hstk (part_sub (by exact hz.o_st0O_3mS_le_L)))),
    by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20],
    by rw [hg _ (by simp), h.x21], by rw [hg _ (by simp), h.x22], ?_⟩
  · rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, _, h2⟩ | rfl
    · exact ⟨scR (H := H) s₀, by simp, Region.sub_prefix (by show j ≤ (H.W + H.S) * 8; omega_using [hj])⟩
    · exact ⟨_, by simp, part_sub h2⟩
    · rw [h.kr.sp]
      exact ⟨_, by simp, fun _ h => h⟩
  · rw [← h.outB]
    exact bytes_keep hf (key (fun o j _ h2 => (hp.o_s.sub_left ho).sub_right (part_sub h2))
      ((hp.o_s.sub_left ho).sub_right low_sub) (by rw [h.kr.sp]; exact (hp.stk_o.sub_right ho).symm))
      (by have := hp.onw; omega_using [hk, this])

/-- What a call leaves. -/
theorem Mid.call (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : Mid hH s₀ k s)
    {ws : List Region} (a : After s ws s')
    (hw : ∀ r ∈ ws, (∃ j, r = ⟨scr s₀, j⟩ ∧ j ≤ 8 * H.W) ∨
      ∃ o j, r = sR s₀ o j ∧ H.stWO ≤ o ∧ o + j ≤ (H.W + H.S) * 8) : Mid hH s₀ k s' :=
  h.keep hp hz hH hk a.rd a.wr a.sp (fun r hr => a.cs r (eregs_pres r hr).1 (eregs_pres r hr).2) a.frame
    fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · rcases hw r hr with h1 | h2
        · exact .inl h1
        · exact .inr (.inl h2)
      · simp only [List.mem_singleton] at hr; exact .inr (.inr hr)

/-- A write into a part of `scratch` from the working state on. -/
theorem Mid.write (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hg : ∀ r ∈ eregs, s'.gpr r = s.gpr r)
    {o n : Nat} (ho : H.stWO ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [sR s₀ o n] s.mem s'.mem) :
    Mid hH s₀ k s' :=
  h.keep hp hz hH hk hrd hwr hsp hg hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl ⟨o, n, rfl, ho, hon⟩)

omit hp hz in
theorem Mid.upd {hH : HashOK H} {k : Nat} {s s' : State} (h : Mid hH s₀ k s) {d : Reg} {v : BitVec 64}
    (u : Upd s s' d v) (hd : d ∉ eregs) : Mid hH s₀ k s' := by
  obtain ne : ∀ r ∈ eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u fun h' => hd (kregs_eregs d h'), u.mem ▸ h.st,
    by rw [u.other _ (ne _ (by simp)), h.x19], by rw [u.other _ (ne _ (by simp)), h.x20],
    by rw [u.other _ (ne _ (by simp)), h.x21], by rw [u.other _ (ne _ (by simp)), h.x22],
    by rw [u.mem, h.outB]⟩

end

/-! ## Copying `T` out -/

theorem outLoop_ok {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 63) (htO : H.tO < 4096) {s : State}
    (hc : s.gpr .x11 = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .x23 + BitVec.ofNat 64 H.tO + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr .x23 + BitVec.ofNat 64 H.tO, n⟩ ⟨s.gpr .x22, n⟩) :
    WP isa H.outLoop s fun t => CopyInv s (s.gpr .x23 + BitVec.ofNat 64 H.tO) (s.gpr .x22) n t := by
  obtain e23 : ∀ {A B : Addr} {k : Nat} {t : State}, CopyInv s A B k t → t.gpr .x23 = s.gpr .x23 :=
    fun h => h.other .x23 (by decide)
  obtain e22 : ∀ {A B : Addr} {k : Nat} {t : State}, CopyInv s A B k t → t.gpr .x22 = s.gpr .x22 :=
    fun h => h.other .x22 (by decide)
  generalize eA : s.gpr .x23 + BitVec.ofNat 64 H.tO = A at hin hsep ⊢
  generalize eB : s.gpr .x22 = B at hout hsep ⊢
  unfold Hash.outLoop
  refine WP.seq (wp_movz fun s₀ u₀ => WP.block_nil ?_)
  obtain i0 : CopyInv s A B 0 s₀ ∧ s₀.gpr .x11 = BitVec.ofNat 64 (n - 0) :=
    ⟨⟨u₀.rd, u₀.wr, u₀.sp, fun r hr => u₀.other r (nm hr .x24), by rw [u₀.gpr]; rfl,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩,
      by rw [u₀.other _ (by decide), hc, Nat.sub_zero]⟩
  refine WP.mono (count_loop hn (by omega_using [hn'])
    (fun k t => CopyInv s A B k t ∧ t.gpr .x11 = BitVec.ofNat 64 (n - k)) (fun k hk t h => ?_) i0)
    fun t h => h.1
  obtain ⟨h, h11⟩ := h
  refine wp_add fun t₁ u₁ => ?_
  refine wp_ldrb (a := A + BitVec.ofNat 64 k) htO
    (by rw [u₁.gpr, e23 h, h.x24, ← eA]; ac_rfl)
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₂ u₂ => ?_
  refine wp_add fun t₃ u₃ => ?_
  refine wp_strb (a := B + BitVec.ofNat 64 k) (by decide)
    (by rw [u₃.gpr, u₂.other .x22 (by decide), u₁.other .x22 (by decide), e22 h, u₂.other .x24 (by decide),
      u₁.other .x24 (by decide), h.x24, eB]; simp)
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ m₄ => ?_
  refine wp_addImm (by decide) fun t₅ u₅ => wp_subImm (by decide) fun t₆ u₆ => WP.block_nil ?_
  obtain h24 : t₅.gpr .x24 = BitVec.ofNat 64 (k + 1) := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x24]
    exact (ofNat_succ k).symm
  obtain x11 : t₆.gpr .x11 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h11, sub_ofNat (by omega_using [hk]), Nat.sub_sub]
  refine ⟨⟨⟨by rw [u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₆.sp, u₅.sp, m₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr => by
      rw [u₆.other r (nm hr .x11), u₅.other r (nm hr .x24), m₄.gpr, u₃.other r (nm hr .x13),
        u₂.other r (nm hr .x9), u₁.other r (nm hr .x12), h.other r hr],
    by rw [u₆.other _ (by decide), h24], ?_⟩, x11⟩, x11⟩
  obtain hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
  obtain v : (t₃.gpr .x9).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, h.mem]
    simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_using [hn']), ↓reduceIte]
    ext i hi; simp
  obtain e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k)) (by rw [hl]; omega_using [hn', hk])
  rw [hl] at e'
  rw [u₆.mem, u₅.mem, m₄.mem, v, u₃.mem, u₂.mem, u₁.mem, h.mem, bytesAt_snoc', e']

/-! ## A step: `U₁` -/

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-- `U₁ = PRF (S ‖ INT (k + 1))`. -/
abbrev U1 (hH : HashOK H) (s₀ : State) (k : Nat) : List Byte :=
  hmacBlockKey hH.SH.H (K0 hH s₀) (saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

omit hp hz in
/-- Before `update` with `INT (k + 1)`. -/
structure AtUpd (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : UpdArgs hH.stream s (A s₀ H.stWO) (A s₀ H.intO) (scr s₀) 4
  x1 : s.gpr .x1 = BitVec.ofNat 64 (H.P.B + sl s₀)
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀)
  int : bytesAt s.mem (A s₀ H.intO) 4 = Spec.Pbkdf2.int (k + 1)

omit hp hz in
/-- Before HMAC's `finalize`. -/
structure AtFin (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : FinArgs (H := H) s (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .x3 + BitVec.ofNat 64 (H.P.B + 4))
    (A s₀ H.uO) (scr s₀)
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

omit hp hz in
/-- Before `iterate`. -/
structure AtIter (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : IterArgs (H := H) s (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO) (scr s₀)
  u : bytesAt s.mem (A s₀ H.uO) H.D = U1 hH s₀ k
  t : bytesAt s.mem (A s₀ H.tO) H.D = U1 hH s₀ k

/-- A copy of the salted inner state, `INT (k + 1)`, and `update`'s arguments. -/
theorem pieceA_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s : State} (h : Mid hH s₀ k s) :
    WP isa (.block H.intArgs) s (AtUpd hH s₀ k) := by
  have hWb := hH.wb_le
  obtain hB := hz.B_le; have hN4 := hz.z.N4; have hD := hz.z.D0; have hD4 := hz.z.D4; have hDN := hz.z.DN
  have hN := hz.N
  obtain hB4 : H.P.B % 4 = 0 := by rcases hz.z.B with h | h <;> exact hz.o_B_mod_4_eq_0
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  obtain eS : 4 * (H.S / 4) = H.S := by exact hz.o_4mSd4_eq_S
  obtain hkD : k * H.D < ol s₀ := (lt_nb hD).1 hk
  obtain hk' := Nat.le_of_lt hkD
  obtain hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD hp.olD; omega_using [hk, this]
  -- The salted inner state, copied.
  simp only [Hash.intArgs, Hash.copy32]
  refine copy32_ok (src := .x23) (dst := .x23) (by decide) (by decide) H.stSO H.stWO (H.S / 4)
    ⟨by exact hz.o_stSO_mod_4_eq_0, by exact hz.o_stSO_4mSd4_le_4096m4⟩ ⟨by exact hz.o_stWO_mod_4_eq_0, by exact hz.o_stWO_4mSd4_le_4096m4⟩ _ s _
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_rw hp hz h.kr (by omega_using [hj, hz.o_stSO_S_le_L]))
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_stWO_S_le_L]))
    (by rw [h.kr.x23, eS]; exact (part_disj hz (Or.inl (by exact hz.o_stSO_S_le_stWO)) (by exact hz.o_stSO_S_le_L) (by exact hz.o_stWO_S_le_L)).sep
          (Region.contains_self _ _) (Region.contains_self _ _))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  rw [h.kr.x23, eS] at m₁
  obtain f₁ : Frame [sR s₀ H.stWO H.S] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain md₁ := h.write hp hz hH hk' rd₁ wr₁ sp₁ (fun r hr => g₁ r (by rintro rfl; revert hr; decide))
    (o := H.stWO) (n := H.S) (Nat.le_refl _) (by exact hz.o_stWO_S_le_L) f₁
  obtain rs₁ : hH.SH.Repr s₁.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀) := by
    rw [m₁]; exact repr_copy hH h.st.s
  -- `INT (k + 1)`.
  refine wp_rev32 fun s₂ u₂ => ?_
  obtain md₂ := md₁.upd u₂ (by decide)
  refine wp_str32 (a := A s₀ H.intO) ⟨by exact hz.o_intO_mod_4_eq_0, by exact hz.o_intO_lt_4096m4⟩ (by rw [md₂.kr.x23])
    (in_sc hp hz md₂.kr.wr (by exact hz.o_intO_4_le_L)) fun s₃ g₃ => ?_
  obtain f₃ : Frame [sR s₀ H.intO 4] s₂.mem s₃.mem := by
    rw [g₃.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain md₃ := md₂.write hp hz hH hk' g₃.rd g₃.wr g₃.sp (fun r _ => by rw [g₃.gpr]) (o := H.intO) (n := 4)
    (by exact hz.o_stWO_le_intO) (by exact hz.o_intO_4_le_L) f₃
  obtain e₃ : s₃.mem = writeBytes s₂.mem (A s₀ H.intO) (Spec.Pbkdf2.int (k + 1)) := by
    rw [g₃.mem, u₂.gpr, setWidth32, md₁.x19,
      show (BitVec.ofNat 64 (k + 1)).setWidth 32 = BitVec.ofNat 32 (k + 1) from
        BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using []),
      show rev32 (BitVec.ofNat 32 (k + 1)) = if true then rev32 (BitVec.ofNat 32 (k + 1)) else _ from rfl,
      writeW32, bytes32_int]
  -- `update`'s arguments.
  refine wp_addImm (by exact hz.o_stWO_lt_4096) fun s₄ u₄ => wp_addImm (by exact hz.o_B_lt_4096) fun s₅ u₅ => wp_addImm (by exact hz.o_intO_lt_4096) fun s₆ u₆ =>
    wp_movz fun s₇ u₇ => wp_mov fun s₈ u₈ => WP.block_nil ?_
  obtain md₈ := ((((md₃.upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)).upd u₈
    (by decide)
  obtain e₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain ua : UpdArgs hH.stream s₈ (A s₀ H.stWO) (A s₀ H.intO) (scr s₀) 4 :=
    { x0 := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.gpr, md₃.kr.x23]
      x2 := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
          u₄.other _ (by decide), md₃.kr.x23]
      x3 := by rw [u₈.other _ (by decide), u₇.gpr]; rfl
      x4 := by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), md₃.kr.x23]
      cd := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := cov_part hp md₈.kr (o := H.intO) (n := 4) (by exact hz.o_intO_4_le_L)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp md₈.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_low hp md₈.kr (by exact hz.o_hsWb_le_L hH)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix hWb)
      d_st := part_disj hz (Or.inr (by exact hz.o_stWO_hsS_le_intO)) (by exact hz.o_intO_4_le_L) (by exact hz.o_stWO_hsS_le_L)
      d_sc := (low_disj hz (by exact hz.o_W8_le_intO) (by exact hz.o_intO_4_le_L)).sub_right (Region.sub_prefix hWb)
      sp16 := by rw [md₈.kr.sp]; exact hp.sp16
      stk_st := stk_sc hp md₈.kr (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_d := stk_sc hp md₈.kr (part_sub (by exact hz.o_intO_4_le_L))
      stk_sc := stk_sc hp md₈.kr (Region.sub_prefix (by exact hz.o_hsWb_le_L hH)) }
  refine ⟨md₈, ua, ?_, by
      rw [e₈]
      exact repr_keep hH f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj hz (Or.inl (by exact hz.o_stWO_S_le_intO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_intO_4_le_L)) (by rw [u₂.mem]; exact rs₁),
    by rw [e₈, e₃, bytesAt_writeBytes_self' (by rfl) (by decide)]⟩
  rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
    md₃.x20, Nat.add_comm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `update` with `INT (k + 1)`. -/
theorem callA_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s : State} (h : AtUpd hH s₀ k s) :
    WP isa (.call H.updN H.updC) s fun t => Mid hH s₀ k t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  obtain hk' : k * H.D ≤ ol s₀ := Nat.le_of_lt ((lt_nb hz.z.D0).1 hk)
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_call hH.stream h.args fun s₁ a₁ r₁ => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_stWO_hsS_le_L⟩
      · exact .inl ⟨_, rfl, hWb⟩
  · have := r₁ _ h.repr (by
      rw [h.x1, List.length_append, xorPad_length, blockKey_length, bytesAt_length])
    rwa [h.int] at this

/-- HMAC's `finalize`'s arguments. -/
theorem finArgs_ok (hH : HashOK H) {k : Nat} {s : State} (h : Mid hH s₀ k s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.block H.finArgs) s (AtFin hH s₀ k) := by
  obtain hD := hz.z.DN; have hN := hz.N
  have hB := hz.B_le
  simp only [Hash.finArgs]
  refine wp_addImm (by exact hz.o_stWO_lt_4096) fun s₁ u₁ => wp_addImm (by exact hz.o_st1O_lt_4096) fun s₂ u₂ => wp_addImm (by exact hz.o_B_4_lt_4096) fun s₃ u₃ =>
    wp_addImm (by exact hz.o_uO_lt_4096) fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  obtain m₅ := ((((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)).upd u₅
    (by decide)
  obtain e₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain stk : ∀ {o n : Nat}, o + n ≤ (H.W + H.S) * 8 → (below s₅.sp 16).Disjoint (sR s₀ o n) :=
    fun h => stk_sc hp m₅.kr (part_sub h)
  obtain fa : FinArgs (H := H) s₅ (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .x3 + BitVec.ofNat 64 (H.P.B + 4))
      (A s₀ H.uO) (scr s₀) :=
    { x0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x1 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
          u₁.other _ (by decide), h.kr.x23]
      x2 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h.x20]
      x3 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.kr.x23]
      x4 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.kr.x23]
      cr := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := cov_part hp m₅.kr (o := H.st1O) (n := H.S) (by exact hz.o_st1O_S_le_L)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp m₅.kr (by exact hz.o_stWO_S_le_L)
        · exact cov_part hp m₅.kr (by exact hz.o_uO_D_le_L)
        · exact cov_low hp m₅.kr (by exact hz.o_W8_le_L)
      i_u := part_disj hz (Or.inr (by exact hz.o_st1O_S_le_stWO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_st1O_S_le_L)
      i_o := part_disj hz (Or.inl (by exact hz.o_stWO_S_le_uO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_uO_D_le_L)
      i_s := low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_S_le_L)
      u_o := part_disj hz (Or.inl (by exact hz.o_st1O_S_le_uO)) (by exact hz.o_st1O_S_le_L) (by exact hz.o_uO_D_le_L)
      u_s := low_disj hz (by exact hz.o_W8_le_st1O) (by exact hz.o_st1O_S_le_L)
      o_s := low_disj hz (by exact hz.o_W8_le_uO) (by exact hz.o_uO_D_le_L)
      sp16 := by rw [m₅.kr.sp]; exact hp.sp16
      stk_i := stk (by exact hz.o_stWO_S_le_L)
      stk_u := stk (by exact hz.o_st1O_S_le_L)
      stk_o := stk (by exact hz.o_uO_D_le_L)
      stk_s := stk_sc hp m₅.kr low_sub
      scnw := by have := hp.snw; omega_using [this] }
  exact ⟨m₅, fa, by rw [e₅]; exact hr⟩

/-- HMAC's `finalize`: `U₁`. -/
theorem callB_ok (hH : HashOK H) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) {k : Nat} (hk : k < nb H s₀) {s : State} (h : AtFin hH s₀ k s) :
    WP isa (.call H.hmacFinN H.hmacFin) s fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.uO) H.D = U1 hH s₀ k := by
  obtain hL := L_lt hz
  obtain hkD : k * H.D < ol s₀ := (lt_nb hz.z.D0).1 hk
  obtain hk' := Nat.le_of_lt hkD
  obtain hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  refine hfin_call hH hF hFd h.args fun s₁ a₁ hpost => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_stWO_S_le_L⟩
      · exact .inr ⟨_, _, rfl, by exact hz.o_stWO_le_uO, by exact hz.o_uO_D_le_L⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · have hK := blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
    exact hpost _ _ hK (by rw [hK, List.length_append, bytesAt_length]; simp [Spec.Pbkdf2.int]; have := hz.o_B_5_le_L; omega_using [hsl, this])
      (by rw [← List.append_assoc]; exact h.repr)
      (by
        rw [List.length_append, bytesAt_length, show (Spec.Pbkdf2.int (k + 1)).length = 4 from rfl]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have : sl s₀ = (s₀.gpr .x3).toNat := rfl
        omega_using [this])
      h.mid.st.o

/-- `U` copied to `T`, and `iterate`'s arguments. -/
theorem pieceC_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s₇ : State} (m₇ : Mid hH s₀ k s₇)
    (hU : bytesAt s₇.mem (A s₀ H.uO) H.D = U1 hH s₀ k) :
    WP isa (.block H.iterArgs) s₇ (AtIter hH s₀ k) := by
  obtain hL := L_lt hz
  obtain hD := hz.z.D0; have hD4 := hz.z.D4; have hDN := hz.z.DN; have hN := hz.N; have hBg := hz.B_ge
  obtain eD : 4 * (H.D / 4) = H.D := by exact hz.o_4mDd4_eq_D
  obtain hkD : k * H.D < ol s₀ := (lt_nb hD).1 hk
  obtain hk' := Nat.le_of_lt hkD
  -- `U` copied to `T`.
  simp only [Hash.iterArgs, Hash.copy32]
  refine copy32_ok (src := .x23) (dst := .x23) (by decide) (by decide) H.uO H.tO (H.D / 4)
    ⟨by exact hz.o_uO_mod_4_eq_0, by exact hz.o_uO_4mDd4_le_4096m4⟩ ⟨by exact hz.o_tO_mod_4_eq_0, by exact hz.o_tO_4mDd4_le_4096m4⟩ _ s₇ _
    (fun j hj => by rw [m₇.kr.x23, add_ofNat]; exact in_rw hp hz m₇.kr (by omega_using [hj, hz.o_uO_D_le_L]))
    (fun j hj => by rw [m₇.kr.x23, add_ofNat]; exact in_sc hp hz m₇.kr.wr (by omega_using [hj, hz.o_tO_D_le_L]))
    (by rw [m₇.kr.x23, eD]; exact (part_disj hz (Or.inl (by exact hz.o_uO_D_le_tO)) (by exact hz.o_uO_D_le_L) (by exact hz.o_tO_D_le_L)).sep
          (Region.contains_self _ _) (Region.contains_self _ _))
    fun s₈ g₈ rd₈ wr₈ sp₈ c₈ => ?_
  rw [m₇.kr.x23, eD] at c₈
  obtain f₈ : Frame [sR s₀ H.tO H.D] s₇.mem s₈.mem := by
    rw [c₈]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain m₈ := m₇.write hp hz hH hk' rd₈ wr₈ sp₈ (fun r hr => g₈ r (by rintro rfl; revert hr; decide))
    (o := H.tO) (n := H.D) (by exact hz.o_stWO_le_tO) (by exact hz.o_tO_D_le_L) f₈
  obtain hU₈ : bytesAt s₈.mem (A s₀ H.uO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D :=
    bytes_keep f₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by exact hz.o_uO_D_le_tO)) (by exact hz.o_uO_D_le_L) (by exact hz.o_tO_D_le_L)) (by exact hz.o_D_le_p64)
  obtain hT₈ : bytesAt s₈.mem (A s₀ H.tO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D := by
    rw [c₈]; exact bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by exact hz.o_D_lt_p64)
  -- `iterate`'s arguments.
  refine wp_addImm (by exact hz.o_st0O_lt_4096) fun s₉ u₉ => wp_addImm (by exact hz.o_uO_lt_4096) fun s₁₀ u₁₀ => ?_
  obtain m₁₀ := (m₈.upd u₉ (by decide)).upd u₁₀ (by decide)
  refine wp_ldr (a := A s₀ H.cO) ⟨by exact hz.o_cO_mod_8_eq_0, by exact hz.o_cO_lt_4096m8⟩ (by rw [m₁₀.kr.x23]) (in_rw hp hz m₁₀.kr (by exact hz.o_cO_8_le_L))
    fun s₁₁ u₁₁ => ?_
  obtain m₁₁ := m₁₀.upd u₁₁ (by decide)
  refine wp_addImm (by exact hz.o_tO_lt_4096) fun s₁₂ u₁₂ => wp_mov fun s₁₃ u₁₃ => WP.block_nil ?_
  obtain m₁₃ := (m₁₁.upd u₁₂ (by decide)).upd u₁₃ (by decide)
  obtain e₁₃ : s₁₃.mem = s₈.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  obtain ia : IterArgs (H := H) s₁₃ (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO)
      (scr s₀) :=
    { x0 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
          u₁₀.other _ (by decide), u₉.gpr, m₈.kr.x23]
      x1 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
          u₉.other _ (by decide), m₈.kr.x23]
      x2 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.mem, u₉.mem, m₈.kr.cW]
      x3 := by rw [u₁₃.other _ (by decide), u₁₂.gpr, m₁₁.kr.x23]
      x4 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), m₁₁.kr.x23]
      cr := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · obtain ⟨r', h', off, e, l⟩ := cov_part hp m₁₃.kr (o := H.st0O) (n := 2 * H.S) (by exact hz.o_st0O_2mS_le_L)
          exact ⟨r', List.mem_append_right _ h', off, e, l⟩
        · obtain ⟨r', h', off, e, l⟩ := cov_part hp m₁₃.kr (o := H.uO) (n := H.D) (by exact hz.o_uO_D_le_L)
          exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp m₁₃.kr (by exact hz.o_tO_D_le_L)
        · exact cov_low hp m₁₃.kr (by exact hz.o_W8_le_L)
      k_t := part_disj hz (Or.inl (by exact hz.o_st0O_2mS_le_tO)) (by exact hz.o_st0O_2mS_le_L) (by exact hz.o_tO_D_le_L)
      k_s := low_disj hz (by exact hz.o_W8_le_st0O) (by exact hz.o_st0O_2mS_le_L)
      u_t := part_disj hz (Or.inl (by exact hz.o_uO_D_le_tO)) (by exact hz.o_uO_D_le_L) (by exact hz.o_tO_D_le_L)
      u_s := low_disj hz (by exact hz.o_W8_le_uO) (by exact hz.o_uO_D_le_L)
      t_s := low_disj hz (by exact hz.o_W8_le_tO) (by exact hz.o_tO_D_le_L)
      knw := by
        have := hp.snw
        obtain e : (A s₀ H.st0O).toNat = (scr s₀).toNat + H.st0O := by
          simp only [A, BitVec.toNat_add, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (a := H.st0O) (by exact hz.o_st0O_lt_p64), Nat.mod_eq_of_lt (by omega_using [hp.snw, hz.o_st0O_2mS_le_L, hz.o_0_lt_S])]
        rw [e]; omega_using [hp.snw, hz.o_st0O_2mS_le_L]
      scnw := by have := hp.snw; omega_using [this] }
  exact ⟨m₁₃, ia, by rw [e₁₃, hU₈, hU], by rw [e₁₃, hT₈, hU]⟩

/-- `iterate`: `T_{k+1}`. -/
theorem callC_ok (hH : HashOK H) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) {k : Nat} (hk : k < nb H s₀) {s : State} (h : AtIter hH s₀ k s) :
    WP isa (.call H.iterN H.iterate) s fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.tO) H.D = Tb hH s₀ (k + 1) := by
  obtain hk' : k * H.D ≤ ol s₀ := Nat.le_of_lt ((lt_nb hz.z.D0).1 hk)
  refine iter_call hH hI hId h.args fun s₁ a₁ hpost => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr ⟨_, _, rfl, by exact hz.o_stWO_le_tO, by exact hz.o_tO_D_le_L⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  obtain hK := blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  obtain hc : ((BitVec.ofNat 64 (cc s₀ - 1)).setWidth 32).toNat = cc s₀ - 1 := by
    have := ((s₀.gpr .x4).setWidth 32).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using []
  obtain hO : A s₀ H.st0O + BitVec.ofNat 64 H.S = A s₀ H.st1O := by
    rw [add_ofNat, show H.st0O + H.S = H.st1O by exact hz.o_st0O_S_eq_st1O]
  obtain ho : hH.SH.Repr s.mem (A s₀ H.st0O + BitVec.ofNat 64 H.S) (xorPad (K0 hH s₀) opad) := by
    rw [hO]; exact h.mid.st.o
  rw [hpost _ hK h.mid.st.i ho, hc, h.u, h.t]
  rfl

/-! ## A step: copying `T` out -/

omit hp in
/-- The bytes of `T` the output still needs: `x21 - D` is negative (its top
bit set) exactly when fewer than `D` are left. -/
theorem outLen_ok {hH : HashOK H} {k : Nat} (hol : ol s₀ < 2 ^ 63) {s : State} (h : Mid hH s₀ k s) :
    WP isa H.outLen s fun t => Mid hH s₀ k t ∧
      t.gpr .x11 = BitVec.ofNat 64 (min (ol s₀ - k * H.D) H.D) ∧ t.mem = s.mem := by
  obtain hD := hz.z.D0; have hDN := hz.z.DN; have hN := hz.N
  unfold Hash.outLen
  refine WP.seq (wp_movz fun s₁ u₁ => wp_subImm (by exact hz.o_D_lt_4096) fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ =>
    WP.block_nil ?_)
  obtain m₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  obtain e₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain x11 : s₃.gpr .x11 = BitVec.ofNat 64 H.D := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, movz_ofNat (by exact hz.o_D_lt_p16)]
  obtain ev : isa.eval (.zero .x .x9) s₃ = some (decide (H.D ≤ ol s₀ - k * H.D)) := by
    change eval (.zero .x .x9) s₃ = _
    rw [eval_zero, u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.x21, shr_beq_zero]
    simp only [Option.some.injEq, decide_eq_decide]
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hol, hDN, hN]
  refine WP.ite _ ev (fun hT => WP.block_nil ⟨m₃, ?_, e₃⟩) fun hF => wp_mov fun s₄ u₄ =>
    WP.block_nil ⟨m₃.upd u₄ (by decide), ?_, by rw [u₄.mem, e₃]⟩
  · rw [x11, Nat.min_eq_right (of_decide_eq_true hT)]
  · have := of_decide_eq_false hF
    rw [u₄.gpr, m₃.x21, Nat.min_eq_left (by omega_using [this])]

/-- Copying as much of `T_{k+1}` as the output needs, and on to the next block. -/
theorem tail_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) (hg : (G hH s₀ k).length = k * H.D) {s : State}
    (h : Mid hH s₀ k s) (ht : bytesAt s.mem (A s₀ H.tO) H.D = Tb hH s₀ (k + 1)) :
    WP isa (.seq H.outLen (.seq H.outLoop (.block Hash.advance))) s fun t =>
      Inv hH s₀ (k + 1) t ∧ isa.eval (.nonzero .x .x21) t = some (decide (k + 1 ≠ nb H s₀)) := by
  obtain hL := L_lt hz
  obtain hD := hz.z.D0; have hDN := hz.z.DN; have hN := hz.N
  obtain hol : ol s₀ < 2 ^ 63 := by have := hp.olD; omega_using [hDN, hN, this]
  obtain hkD : k * H.D < ol s₀ := (lt_nb hD).1 hk
  obtain hk1 := lt_nb (s₀ := s₀) hD (k := k + 1)
  rw [Nat.succ_mul] at hk1
  have hon := hp.onw
  generalize en : min (ol s₀ - k * H.D) H.D = n
  obtain hn : 0 < n ∧ n ≤ H.D ∧ k * H.D + n ≤ ol s₀ := by omega_using [hD, hkD, en]
  obtain hdn : done H s₀ (k + 1) = k * H.D + n := by
    show min ((k + 1) * H.D) (ol s₀) = _; rw [Nat.succ_mul]; omega_using [en, hn]
  obtain osub : Region.Sub ⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ (outR s₀) := Offset.sub_base _ hn.2.2
  refine WP.seq (WP.mono (outLen_ok hz hol h) fun s₁ ⟨m₁, rc₁, e₁⟩ => ?_)
  rw [en] at rc₁
  refine WP.seq (WP.mono (outLoop_ok (n := n) hn.1 (by omega_using [hol, hn]) (by exact hz.o_tO_lt_4096) rc₁
    (fun j hj => by rw [m₁.kr.x23, add_ofNat]; exact in_rw hp hz m₁.kr (by omega_using [hj, hn.2.1, hz.o_tO_D_le_L]))
    (fun j hj => by
      rw [m₁.x22, add_ofNat]
      exact ⟨outR s₀, by rw [m₁.kr.wr, hp.wr]; simp, Offset.contains_base _ (by omega_using [hn, hj]) (by omega_using [hon, hn, hj])⟩)
    (by rw [m₁.kr.x23, m₁.x22]; exact ((hp.o_s.sub_left osub).sub_right (part_sub (by omega_using [hn.2.1, hz.o_tO_D_le_L]))).symm))
    fun s₂ c₂ => ?_)
  rw [m₁.kr.x23, m₁.x22] at c₂
  obtain f₂ : Frame [(⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)] s₁.mem s₂.mem := by
    rw [c₂.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain od : ∀ {X : Region}, Region.Sub X (scR (H := H) s₀) →
      ∀ r ∈ [(⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)], X.Disjoint r := fun hX r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hp.o_s.sub_left osub).sub_right hX).symm
  obtain k₂ : KR (H := H) s₀ s₂ := m₁.kr.keep c₂.rd c₂.wr c₂.sp (fun r hr => c₂.other r (kregs_clob r hr)) f₂
    (od (part_sub (by exact hz.o_sv_80_le_L))) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩
  obtain g₂ : ∀ r ∈ eregs, s₂.gpr r = s₁.gpr r := fun r hr => c₂.other r (eregs_clob r hr)
  refine wp_add fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ?_
  obtain e₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  obtain x21 : s₅.gpr .x21 = BitVec.ofNat 64 (ol s₀ - done H s₀ (k + 1)) := by
    rw [u₅.gpr, u₄.other .x21 (by decide), u₄.other .x24 (by decide), u₃.other .x21 (by decide),
      u₃.other .x24 (by decide), g₂ _ (by decide), c₂.x24, m₁.x21, sub_ofNat (by omega_using [hn]), hdn, Nat.sub_sub]
  refine ⟨⟨((k₂.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide), ?_, ?_, ?_, x21, ?_, ?_, ?_⟩, ?_⟩
  · rw [e₅]; exact m₁.st.keep hz hH f₂ (od (part_sub (by exact hz.o_st0O_3mS_le_L)))
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide), m₁.x19]
    exact (ofNat_succ _).symm
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), m₁.x20]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂ _ (by decide), c₂.x24, m₁.x22, add_ofNat,
      hdn]
  · rw [G_succ, List.length_append, hg, ← ht, bytesAt_length, Nat.succ_mul]
  · rw [e₅, hdn, bytesAt_add, bytes_keep f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hon, hn])).symm)
      (by omega_using [hon, hn]),
      c₂.mem, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hol, hn]),
      m₁.outB, G_succ, ← hg, List.take_length_add_append, ← ht, e₁, ← bytesAt_take _ _ hn.2.1]
  · change eval (.nonzero .x .x21) s₅ = _
    rw [eval_nonzero, x21, ofNat_ne_zero (by omega_using [hon, hn, hdn])]
    simp only [Option.some.injEq, decide_eq_decide]
    omega_using [hk, hk1, en, hdn]

/-! ## The loop and `pbkdf2` -/

/-- One block of the output. -/
theorem block_ok (hH : HashOK H) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) {k : Nat} (hk : k < nb H s₀) {s : State} (h : Inv hH s₀ k s) :
    WP isa H.block s fun t =>
      Inv hH s₀ (k + 1) t ∧ isa.eval (.nonzero .x .x21) t = some (decide (k + 1 ≠ nb H s₀)) := by
  obtain hkD : k * H.D < ol s₀ := (lt_nb hz.z.D0).1 hk
  obtain hd : done H s₀ k = k * H.D := by show min _ _ = _; omega_using [hkD]
  have hb := h.outB
  rw [hd, List.take_of_length_le (Nat.le_of_eq h.glen)] at hb
  obtain m : Mid hH s₀ k s := ⟨h.kr, h.st, h.x19, h.x20, by rw [h.x21, hd], by rw [h.x22, hd], hb⟩
  unfold Hash.block
  refine WP.seq (WP.mono (pieceA_ok hp hz hH hk m) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (callA_ok hp hz hH hk h₁) fun s₂ ⟨m₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (finArgs_ok hp hz hH m₂ r₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (callB_ok hp hz hH hF hFd hk h₃) fun s₄ ⟨m₄, u₄⟩ => ?_)
  refine WP.seq (WP.mono (pieceC_ok hp hz hH hk m₄ u₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (callC_ok hp hz hH hI hId hk h₅) fun s₆ ⟨m₆, t₆⟩ => ?_)
  exact tail_ok hp hz hH hk h.glen m₆ t₆

/-- The loop over the blocks of the output: none when `out_len = 0`. -/
theorem loop_ok (hH : HashOK H) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) {s : State} (h : Inv hH s₀ 0 s)
    (hz0 : isa.eval (.zero .x .x21) s = some (decide (ol s₀ = 0))) :
    WP isa (.ite (.zero .x .x21) (.block []) (.loop H.block (.nonzero .x .x21))) s (Inv hH s₀ (nb H s₀)) := by
  have hD := hz.z.D0
  refine WP.ite (decide (ol s₀ = 0)) hz0 (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · rw [(nb_zero hD).2 (of_decide_eq_true h0)]; exact h
  · have : nb H s₀ ≠ 0 := fun e => by simp [(nb_zero hD).1 e] at h0
    exact nb_loop (Nat.pos_of_ne_zero this) (Inv hH s₀)
      (fun k hk t ht => block_ok hp hz hH hF hFd hI hId hk ht) h

theorem correct (hH : HashOK H) (hIn : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hInd : H.hmacInit.aarch64Depth ≤ 1) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) :
    WP isa H.pbkdf2 s₀ fun s' => abiPreserved s₀ s' ∧ (pbkG hH.SH (H.W + H.S)).post s₀ s' := by
  apply WP.withPreservedV (hc := hH.pbkdf2_keepsV)
  obtain hD := hz.z.D0; have hW := hz.W
  unfold Hash.pbkdf2
  refine WP.seq (WP.mono (entry_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (key_ok hp hz hH k₁) fun s₂ ⟨k₂, x2₂, x3₂, ka⟩ => ?_)
  refine WP.seq (WP.mono (setup_ok hp hz hH hIn hInd k₂ x2₂ x3₂ ka) fun s₃ ⟨k₃, st₃⟩ => ?_)
  refine WP.seq (WP.mono (loopRegs_ok hp hz hH k₃ st₃) fun s₄ ⟨i₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hp hz hH hF hFd hI hId i₄ z₄) fun s₅ i₅ => ?_)
  have k₅ := i₅.kr
  unfold Hash.exit
  refine WP.mono (restore_ok H.hh k₅.x23 (by show H.W ≤ 1024; exact hz.o_W_le_1024) k₅.saved (in_wr hp k₅)
    (by have : H.S = H.P.N + H.P.B := rfl; have := hz.B_ge; show 8 * H.W + 56 ≤ (H.W + H.S) * 8; exact hz.o_W8_56_le_L))
    fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hsp, k₅.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hg _ (by decide)
      | exact (ho _ (by decide)).trans (k₅.cs _ (by decide))
  obtain hdone : done H s₀ (nb H s₀) = ol s₀ := by
    have := ol_le (s₀ := s₀) hD; show min _ _ = _; omega_using [this]
  have hb := i₅.outB
  rw [hdone] at hb
  show Spec.Pbkdf2.pbkdf2Hmac hH.SH (bytesAt s₀.mem (pw s₀) (pwl s₀)) (saltB s₀) (cc s₀) (ol s₀) =
    some (bytesAt s'.mem (out s₀) (ol s₀))
  have hol := hp.olD
  rw [Spec.Pbkdf2.pbkdf2Hmac, hH.hD, Spec.Pbkdf2.pbkdf2, ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [hol])), hm,
    hb]
  rfl

end

end VG.Proof.Pbkdf2.Md.AArch64.Pbk
