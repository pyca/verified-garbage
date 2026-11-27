module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Common
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Pbkdf2.Md.X86_64.Pbkdf2`, which this module and modules that import it used -/

section

/-! ### `Pbkdf2.Md.X86_64.PbkCalls`, which this module and modules that import it used -/

section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`'s calls

The calls of HMAC's `init` and `finalize` and of `iterate`, whose contracts
(`initG`, `finG`, `iterK`) their proofs are given as hypotheses: each is run
with `WP.call`, and shown constant time in two runs with `RelCT.call`. Each
uses at most 24 bytes of stack below `rsp` (a call two deep).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG ne_rsp callEntry_bytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash} (hH : HashOK H)

theorem ret24 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp, 8⟩ (below (s.gpr .rsp) 24) := by
  rw [State.callEntry_rsp]; exact Offset.sub_below _ (a := 8) (by omega_using []) (by omega_using [])

theorem stk24 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp - 16, 16⟩ (below (s.gpr .rsp) 24) := by
  rw [State.callEntry_rsp, show s.gpr .rsp - 8 - 16 = s.gpr .rsp - BitVec.ofNat 64 24 from
    Offset.sub_sub_ofNat _ 8 16]
  exact Offset.sub_below _ (a := 24) (by omega_using []) (by omega_using [])

theorem stk8 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp - 8, 8⟩ (below (s.gpr .rsp) 24) := by
  rw [State.callEntry_rsp, show s.gpr .rsp - 8 - 8 = s.gpr .rsp - BitVec.ofNat 64 16 from
    Offset.sub_sub_ofNat _ 8 8]
  exact Offset.sub_below _ (a := 16) (by omega_using []) (by omega_using [])

theorem b16 (s : State) : Region.Sub (below (s.gpr .rsp) 16) (below (s.gpr .rsp) 24) :=
  below_sub (by omega_using []) (by omega_using [])

/-- The bytes of a region outside the 24 bytes below `rsp` read the same on
entry to a callee. -/
theorem entry_bytes (s : State) {p : Addr} {n : Nat} (hd : (below (s.gpr .rsp) 24).Disjoint ⟨p, n⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt s.callEntry.mem p n = bytesAt s.mem p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => callEntry_bytes s (hd.sub_left (b16 s)) hn (List.mem_range.mp hi)

/-- A streaming state outside the 24 bytes below `rsp` represents the same
message on entry to a callee. -/
theorem entry_repr (s : State) {p : Addr} (hd : (below (s.gpr .rsp) 24).Disjoint ⟨p, H.S⟩) {m : List Byte}
    (h : hH.SH.Repr s.mem p m) : hH.SH.Repr s.callEntry.mem p m :=
  hH.stream.repr _ _ _ _ _ (fun i hi => callEntry_bytes s (hd.sub_left (b16 s))
    (by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 2 ^ 64; omega_arith) hi) h

/-! ## HMAC's `init` -/

/-- The regions of a call of HMAC's `init`. -/
structure InitArgs (s : State) (inn out k sc : Addr) (kl : Nat) : Prop where
  rdi : s.gpr .rdi = inn
  rsi : s.gpr .rsi = out
  rdx : s.gpr .rdx = k
  rcx : (s.gpr .rcx).toNat = kl
  r8 : s.gpr .r8 = sc
  klB : kl ≤ H.P.B
  cr : Covers [⟨k, kl⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨out, H.S⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨out, H.S⟩ ⟨sc, 8 * H.W⟩
  k_i : Region.Disjoint ⟨k, kl⟩ ⟨inn, H.S⟩
  k_o : Region.Disjoint ⟨k, kl⟩ ⟨out, H.S⟩
  k_s : Region.Disjoint ⟨k, kl⟩ ⟨sc, 8 * H.W⟩
  stk_i : (below (s.gpr .rsp) 24).Disjoint ⟨inn, H.S⟩
  stk_o : (below (s.gpr .rsp) 24).Disjoint ⟨out, H.S⟩
  stk_k : (below (s.gpr .rsp) 24).Disjoint ⟨k, kl⟩
  stk_s : (below (s.gpr .rsp) 24).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem covers_app {rd wr : List Region} {s : State} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ wr) (s.rd ++ s.wr) := fun a n hi => by
  obtain ⟨r, hr', hc⟩ := hi
  rcases List.mem_append.mp hr' with h | h
  · exact hr a n ⟨r, h, hc⟩
  · obtain ⟨r'', h'', hc''⟩ := hw a n ⟨r, h, hc⟩
    exact ⟨r'', List.mem_append_right _ h'', hc''⟩

theorem InitArgs.pre {s : State} {inn out k sc : Addr} {kl : Nat} (a : InitArgs (H := H) s inn out k sc kl) :
    (initG hH.SH H.W).pre (s.callEntry.withRegions [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hB := hH.hB
  simp only [initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, a.r8, hS, hB]
  exact ⟨a.klB, trivial, trivial, a.i_o, a.i_s, a.o_s, a.k_i, a.k_o, a.k_s,
    a.stk_i.sub_left (ret24 s), a.stk_o.sub_left (ret24 s), a.stk_s.sub_left (ret24 s),
    a.stk_i.sub_left (stk24 s), a.stk_o.sub_left (stk24 s), a.stk_k.sub_left (stk24 s),
    a.stk_s.sub_left (stk24 s), a.scnw⟩

theorem hinit_call (hv : Verified X86_64.target H.hmacInit (initG hH.SH H.W)) (hsp : NoSp H.hmacInit)
    (hd : H.hmacInit.depth ≤ 2) {s : State} {inn out k sc : Addr} {kl : Nat}
    (a : InitArgs (H := H) s inn out k sc kl) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] ++ [below (s.gpr .rsp) 24]) s.mem s'.mem →
      hH.SH.Repr s'.mem inn (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) ipad) →
      hH.SH.Repr s'.mem out (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa (.call H.hmacInitN H.hmacInit) s Q := by
  refine WP.call hv.1 hsp (by omega_using [hd]) (a.pre hH) (covers_app a.cr a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  have e : bytesAt s.callEntry.mem k kl = bytesAt s.mem k kl :=
    entry_bytes s a.stk_k (by have := a.klB; have := hH.B_le; omega_arith)
  simp only [initG, State.withRegions_gpr, State.withRegions_mem, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, hm, e] at hpost
  exact hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by omega_using [hd]) (by omega_using [])) hpost.1 hpost.2

theorem hinit_rel (hv : Verified X86_64.target H.hmacInit (initG hH.SH H.W)) {P : State → State → Prop}
    {inn out k sc : Addr} {kl : Nat}
    (h : ∀ s s', P s s' → InitArgs (H := H) s inn out k sc kl ∧ InitArgs (H := H) s' inn out k sc kl ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.hmacInitN H.hmacInit) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  have cx : s.gpr .rcx = s'.gpr .rcx := BitVec.eq_of_toNat_eq (by rw [a.rcx, a'.rcx])
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw, sp⟩
  simp only [initG, State.withRegions_gpr, State.callEntry_rsp, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a'.rdi, a.rsi, a'.rsi,
    a.rdx, a'.rdx, a.r8, a'.r8, cx, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## HMAC's `finalize` -/

/-- The regions of a call of HMAC's `finalize`. -/
structure FinArgs (s : State) (inn outer cnt o sc : Addr) : Prop where
  rdi : s.gpr .rdi = inn
  rsi : s.gpr .rsi = outer
  rdx : s.gpr .rdx = cnt
  rcx : s.gpr .rcx = o
  r8 : s.gpr .r8 = sc
  cr : Covers [⟨outer, H.S⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_u : Region.Disjoint ⟨inn, H.S⟩ ⟨outer, H.S⟩
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨o, H.D⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  u_o : Region.Disjoint ⟨outer, H.S⟩ ⟨o, H.D⟩
  u_s : Region.Disjoint ⟨outer, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨o, H.D⟩ ⟨sc, 8 * H.W⟩
  stk_i : (below (s.gpr .rsp) 24).Disjoint ⟨inn, H.S⟩
  stk_u : (below (s.gpr .rsp) 24).Disjoint ⟨outer, H.S⟩
  stk_o : (below (s.gpr .rsp) 24).Disjoint ⟨o, H.D⟩
  stk_s : (below (s.gpr .rsp) 24).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem FinArgs.pre {s : State} {inn outer cnt o sc : Addr} (a : FinArgs (H := H) s inn outer cnt o sc) :
    (finG hH.SH H.W).pre (s.callEntry.withRegions [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hD := hH.hD
  simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rsi ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a.rsi, a.rcx, a.r8, hS, hD]
  exact ⟨trivial, trivial, a.i_u, a.i_o, a.i_s, a.u_o, a.u_s, a.o_s,
    a.stk_i.sub_left (ret24 s), a.stk_u.sub_left (ret24 s), a.stk_o.sub_left (ret24 s),
    a.stk_s.sub_left (ret24 s), a.stk_i.sub_left (stk24 s), a.stk_u.sub_left (stk24 s),
    a.stk_o.sub_left (stk24 s), a.stk_s.sub_left (stk24 s), a.scnw⟩

theorem hfin_call (hv : Verified X86_64.target H.hmacFin (finG hH.SH H.W)) (hsp : NoSp H.hmacFin)
    (hd : H.hmacFin.depth ≤ 2) {s : State} {inn outer cnt o sc : Addr}
    (a : FinArgs (H := H) s inn outer cnt o sc) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] ++ [below (s.gpr .rsp) 24]) s.mem s'.mem →
      (∀ k0 text, k0.length = H.P.B → k0.length + text.length < 2 ^ 64 →
        hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) → cnt = BitVec.ofNat 64 (H.P.B + text.length) →
        hH.SH.Repr s.mem outer (xorPad k0 opad) → bytesAt s'.mem o H.D = hmacBlockKey hH.SH.H k0 text) →
      Q s') :
    WP isa (.call H.hmacFinN H.hmacFin) s Q := by
  refine WP.call hv.1 hsp (by omega_using [hd]) (a.pre hH) (covers_app a.cr a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  refine hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by omega_using [hd]) (by omega_using [])) fun k0 text hk hl hi hc ho => ?_
  have hS := hH.hS; have hD := hH.hD; have hB := hH.hB
  simp only [finG, State.withRegions_gpr, State.withRegions_mem, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, hm, hD, hB] at hpost
  exact hpost k0 text hk hl (entry_repr hH s a.stk_i hi) hc (entry_repr hH s a.stk_u ho)

theorem hfin_rel (hv : Verified X86_64.target H.hmacFin (finG hH.SH H.W)) {P : State → State → Prop}
    {inn outer cnt o sc : Addr}
    (h : ∀ s s', P s s' → FinArgs (H := H) s inn outer cnt o sc ∧ FinArgs (H := H) s' inn outer cnt o sc ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.hmacFinN H.hmacFin) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw, sp⟩
  simp only [finG, State.withRegions_gpr, State.callEntry_rsp, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a'.rdi, a.rsi, a'.rsi,
    a.rdx, a'.rdx, a.rcx, a'.rcx, a.r8, a'.r8, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `iterate` -/

/-- The regions of a call of `iterate`. -/
structure IterArgs (s : State) (key u : Addr) (n : BitVec 64) (t sc : Addr) : Prop where
  rdi : s.gpr .rdi = key
  rsi : s.gpr .rsi = u
  rdx : s.gpr .rdx = n
  rcx : s.gpr .rcx = t
  r8 : s.gpr .r8 = sc
  cr : Covers [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] (s.rd ++ s.wr)
  cw : Covers [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  k_t : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨t, H.D⟩
  k_s : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨sc, 8 * H.W⟩
  u_t : Region.Disjoint ⟨u, H.D⟩ ⟨t, H.D⟩
  u_s : Region.Disjoint ⟨u, H.D⟩ ⟨sc, 8 * H.W⟩
  t_s : Region.Disjoint ⟨t, H.D⟩ ⟨sc, 8 * H.W⟩
  stk_k : (below (s.gpr .rsp) 24).Disjoint ⟨key, 2 * H.S⟩
  stk_u : (below (s.gpr .rsp) 24).Disjoint ⟨u, H.D⟩
  stk_t : (below (s.gpr .rsp) 24).Disjoint ⟨t, H.D⟩
  stk_s : (below (s.gpr .rsp) 24).Disjoint ⟨sc, 8 * H.W⟩
  knw : key.toNat + 2 * H.S ≤ 2 ^ 64
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem IterArgs.pre {s : State} {key u t sc : Addr} {n : BitVec 64} (a : IterArgs (H := H) s key u n t sc) :
    (iterK hH.SH H.W).pre (s.callEntry.withRegions [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hD := hH.hD
  simp only [iterK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rsi ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a.rsi, a.rcx, a.r8, hS, hD]
  exact ⟨trivial, trivial, a.k_t, a.k_s, a.u_t, a.u_s, a.t_s,
    a.stk_k.sub_left (ret24 s), a.stk_u.sub_left (ret24 s), a.stk_t.sub_left (ret24 s),
    a.stk_s.sub_left (ret24 s), a.stk_k.sub_left (stk8 s), a.stk_u.sub_left (stk8 s),
    a.stk_t.sub_left (stk8 s), a.stk_s.sub_left (stk8 s), a.knw, a.scnw⟩

theorem iter_call (hv : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hsp : NoSp H.iterate)
    (hd : H.iterate.depth ≤ 2) {s : State} {key u t sc : Addr} {n : BitVec 64}
    (a : IterArgs (H := H) s key u n t sc) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] ++ [below (s.gpr .rsp) 24]) s.mem s'.mem →
      (∀ k0, k0.length = H.P.B → hH.SH.Repr s.mem key (xorPad k0 ipad) →
        hH.SH.Repr s.mem (key + BitVec.ofNat 64 H.S) (xorPad k0 opad) →
        bytesAt s'.mem t H.D = Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (n.setWidth 32).toNat
          (bytesAt s.mem u H.D) (bytesAt s.mem t H.D)) →
      Q s') :
    WP isa (.call H.iterN H.iterate) s Q := by
  refine WP.call hv.1 hsp (by omega_using [hd]) (a.pre hH) (covers_app a.cr a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  refine hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by omega_using [hd]) (by omega_using [])) fun k0 hk hi ho => ?_
  have hS := hH.hS; have hD := hH.hD; have hB := hH.hB
  have hS2 : H.S ≤ 256 := by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 256; omega_arith
  have hDn : H.D ≤ 2 ^ 64 := by have := hH.hDN; have := hH.N_le; omega_arith
  simp only [iterK, State.withRegions_gpr, State.withRegions_mem, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, hm, hD, hB, hS,
    entry_bytes s a.stk_u hDn, entry_bytes s a.stk_t hDn] at hpost
  have eS : H.S = H.P.N + H.P.B := rfl
  refine hpost k0 hk (entry_repr hH s (a.stk_k.sub_right (Region.sub_prefix (by omega_using []))) hi)
    (entry_repr hH s (a.stk_k.sub_right (Offset.sub_base _ (by omega_using [eS]))) ho)

theorem iter_rel (hv : Verified X86_64.target H.iterate (iterK hH.SH H.W)) {P : State → State → Prop}
    {key u t sc : Addr} {n : BitVec 64}
    (h : ∀ s s', P s s' → IterArgs (H := H) s key u n t sc ∧ IterArgs (H := H) s' key u n t sc ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.iterN H.iterate) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw, sp⟩
  simp only [iterK, State.withRegions_gpr, State.callEntry_rsp, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a'.rdi, a.rsi, a'.rsi,
    a.rdx, a'.rdx, a.rcx, a'.rcx, a.r8, a'.r8, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.Pbkdf2.Md.X86_64.Pbk

end

end

/-! ### `Pbkdf2.Md.X86_64.PbkCommon`, which only this module used -/

section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`'s parts

The precondition of `pbkdf2` (`Pre`), the parts of its `scratch`, what every
piece of it keeps (`KR`), and the calls of the functions it calls: the hash
function's streaming functions (`VG.Proof.Pbkdf2.Md.X86_64.Calls.StreamOK`), HMAC's
`init` and `finalize`, and `iterate`, whose proofs it takes as hypotheses.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Sizes pbkG)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG After SavedRegs ne_rsp callEntry_bytes SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep sub_of_off sub_of_self)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev pw : Addr := s₀.gpr .rdi
abbrev pwl : Nat := (s₀.gpr .rsi).toNat
abbrev salt : Addr := s₀.gpr .rdx
abbrev sl : Nat := (s₀.gpr .rcx).toNat
/-- The iteration count. -/
abbrev cc : Nat := ((s₀.gpr .r8).setWidth 32).toNat
abbrev out : Addr := s₀.gpr .r9
abbrev ol : Nat := (stackArg s₀ 0).toNat
abbrev scr : Addr := stackArg s₀ 1
abbrev pwR : Region := ⟨pw s₀, pwl s₀⟩
abbrev saltR : Region := ⟨salt s₀, sl s₀⟩
abbrev outR : Region := ⟨out s₀, ol s₀⟩
abbrev scR : Region := ⟨scr s₀, (H.W + H.S) * 8⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := ⟨s₀.gpr .rsp - BitVec.ofNat 64 24, 24⟩
/-- An address in `scratch`, and a part of it. -/
abbrev A (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- Our caller's registers, `out` and `c - 1`. -/
abbrev hdrR : Region := sR s₀ H.sv 64
/-- The working space of the functions we call. -/
abbrev lowR : Region := ⟨scr s₀, 8 * H.W⟩

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  sp₁ : 24 ≤ (s₀.gpr .rsp).toNat
  sp₂ : (s₀.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s₀.rd = [pwR s₀, saltR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scR (H := H) s₀]
  pw_o : (pwR s₀).Disjoint (outR s₀)
  pw_s : (pwR s₀).Disjoint (scR (H := H) s₀)
  sa_o : (saltR s₀).Disjoint (outR s₀)
  sa_s : (saltR s₀).Disjoint (scR (H := H) s₀)
  o_s : (outR s₀).Disjoint (scR (H := H) s₀)
  o_a : (outR s₀).Disjoint (argR s₀)
  s_a : (scR (H := H) s₀).Disjoint (argR s₀)
  ret_pw : (retR s₀).Disjoint (pwR s₀)
  ret_sa : (retR s₀).Disjoint (saltR s₀)
  ret_o : (retR s₀).Disjoint (outR s₀)
  ret_s : (retR s₀).Disjoint (scR (H := H) s₀)
  ret_a : (retR s₀).Disjoint (argR s₀)
  stk_pw : (stkR s₀).Disjoint (pwR s₀)
  stk_sa : (stkR s₀).Disjoint (saltR s₀)
  stk_o : (stkR s₀).Disjoint (outR s₀)
  stk_s : (stkR s₀).Disjoint (scR (H := H) s₀)
  stk_a : (stkR s₀).Disjoint (argR s₀)
  pwnw : (pw s₀).toNat + pwl s₀ ≤ 2 ^ 64
  sanw : (salt s₀).toNat + sl s₀ ≤ 2 ^ 64
  onw : (out s₀).toNat + ol s₀ ≤ 2 ^ 64
  snw : (scr s₀).toNat + (H.W + H.S) * 8 ≤ 2 ^ 64
  c0 : 0 < cc s₀
  olD : ol s₀ ≤ (2 ^ 32 - 1) * H.D

theorem pre_of (hH : HashOK H) {s₀ : State} (h : (pbkG hH.SH (H.W + H.S)).pre s₀) : Pre (H := H) s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩ := h
  have hD := hH.hD
  simp only [hD] at h26
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩

/-- The sizes, as facts about natural numbers. -/
structure PSizes (H : Hash) : Prop where
  z : Sizes H
  W : H.W ≤ 256

theorem _root_.VG.Proof.Pbkdf2.Md.X86_64.HashOK.psizes (hH : HashOK H) : PSizes H := ⟨hH.sizes, hH.hW⟩

/-! ## The parts of `scratch` -/

/-- Where the parts of `scratch` are. -/
theorem layout : H.sv = 8 * H.W ∧ H.outO = 8 * H.W + 48 ∧ H.cO = 8 * H.W + 56 ∧ H.st0O = 8 * H.W + 64 ∧
    H.st1O = 8 * H.W + 64 + H.S ∧ H.stSO = 8 * H.W + 64 + 2 * H.S ∧ H.stWO = 8 * H.W + 64 + 3 * H.S ∧
    H.uO = 8 * H.W + 64 + 4 * H.S ∧ H.tO = 8 * H.W + 64 + 4 * H.S + H.D ∧
    H.hkO = 8 * H.W + 64 + 4 * H.S + 2 * H.D ∧ H.intO = 8 * H.W + 64 + 4 * H.S + 2 * H.D + H.P.N ∧
    H.S = H.P.N + H.P.B := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [Hash.sv, Hash.st0O, Hash.st1O, Hash.stSO, Hash.stWO, Hash.uO, Hash.tO,
      Hash.hkO, Hash.intO] <;> omega_using []

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)

include hz in
/-- The parts of `scratch`, as offsets: they end before its end. -/
theorem end_le : H.intO + 4 ≤ (H.W + H.S) * 8 := by
  have := hz.z.N; have := hz.z.D; have := hz.z.B; have := layout (H := H)
  omega_arith

include hz in
theorem L_lt : (H.W + H.S) * 8 < 2 ^ 64 := by
  have := hz.W; have := hz.z.N; have := hz.z.B_le; show (H.W + (H.P.N + H.P.B)) * 8 < 2 ^ 64; omega_arith

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

theorem stk_ret : (stkR s₀).Disjoint (retR s₀) :=
  fun x h₁ h₂ => Offset.base_disjoint_below (s₀.gpr .rsp) (n := 24) (k := 8) (by omega_using []) x h₂ h₁

/-- The 8 · (depth + 1) bytes below `rsp` that a call of depth at most 2 uses. -/
theorem below_stk {n : Nat} (hn : n ≤ 24) : Region.Sub (below (s₀.gpr .rsp) n) (stkR s₀) :=
  below_sub hn (by omega_using [])

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the entry on: our caller's registers,
`out` and `c - 1` in `scratch`, and everything written is in `out`,
`scratch` or the stack. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H.hh (scr s₀) s₀ s.mem
  outW : s.mem.readW (A s₀ H.outO) 64 = out s₀
  cW : s.mem.readW (A s₀ H.cO) 64 = BitVec.ofNat 64 (cc s₀ - 1)
  frame : Frame [outR s₀, scR (H := H) s₀, stkR s₀] s₀.mem s.mem

/-- Registers `KR` fixes. -/
abbrev kregs : List Reg := [.r15, .rsp]

theorem hdr_sub {s₀ : State} {o : Nat} (h₁ : H.sv ≤ o) (h₂ : o + 8 ≤ H.sv + 64) :
    Region.Sub ⟨A s₀ o, 8⟩ (hdrR (H := H) s₀) := Offset.sub _ h₁ h₂

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp hz in
theorem KR.keep {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (hdrR (H := H) s₀).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [outR s₀, scR (H := H) s₀, stkR s₀], Region.Sub r r') :
    KR (H := H) s₀ s' := by
  obtain hs : Region.Sub (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H.hh (scr s₀)) (hdrR (H := H) s₀) := Offset.sub _ (Nat.le_refl _) (by
    show 8 * H.W + 48 ≤ 8 * H.W + 64; omega_using [])
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.rsp, h15.trans h.r15,
    SavedRegs.frame H.hh h.saved hf fun r hr => (hd r hr).sub_left hs, ?_, ?_, h.frame.trans (hf.sub hsub)⟩
  · rw [← h.outW]
    exact hf.readW (r := ⟨A s₀ H.outO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.outO]) (by simp [Hash.outO])))
      (by decide)
  · rw [← h.cW]
    exact hf.readW (r := ⟨A s₀ H.cO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.cO]) (by simp [Hash.cO])))
      (by decide)

omit hp in
/-- A write into a part of `scratch` after its header keeps `KR`. -/
theorem KR.write {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) {o n : Nat}
    (ho : H.st0O ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [sR s₀ o n] s.mem s'.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp h15 hf
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by simpa [Hash.st0O] using ho)) (by
        have := end_le hz; simp only [Hash.st0O] at ho; omega_using [ho, hon]) hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, part_sub hon⟩)

/-- What a call leaves, writing parts of `scratch` after its header, or its
working space, and the stack below `rsp`. -/
theorem KR.call {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {ws : List Region} {n : Nat} (hn : n ≤ 24)
    (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) :
    KR (H := H) s₀ s' := by
  have := end_le hz; have := layout (H := H)
  obtain hst : H.sv + 64 = H.st0O := by simp [Hash.st0O]
  refine h.keep hrd hwr (hcs _ (by simp [calleeSaved])) (hcs _ (by simp [calleeSaved])) hf
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact (low_disj hz (Nat.le_refl _) (by omega_arith)).sub_right (Region.sub_prefix hk)
      · exact part_disj hz (Or.inl (by rw [hst]; exact h₁)) (by rw [hst]; omega_using [h₁, h₂]) h₂
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.rsp]
      exact ((hp.stk_s.sub_left (below_stk hn)).sub_right (part_sub (by rw [hst]; omega_arith))).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact ⟨scR (H := H) s₀, by simp, Region.sub_prefix (by show k ≤ (H.W + H.S) * 8; omega_using [hk])⟩
      · exact ⟨_, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.rsp]
      exact ⟨_, by simp, below_stk hn⟩

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

omit hp hz in
theorem KR.readW {s : State} (h : KR (H := H) s₀ s) {R : Region} {a : Addr} (hc : R.Contains a 8)
    (hd : ∀ r ∈ [outR s₀, scR (H := H) s₀, stkR s₀], R.Disjoint r) :
    s.mem.readW a 64 = s₀.mem.readW a 64 :=
  h.frame.readW hc hd (by decide)

omit hz in
theorem KR.ret {s : State} (h : KR (H := H) s₀ s) :
    s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
  h.readW (R := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s
    · exact stk_ret.symm)

omit hz in
/-- `out_len`, on the stack. -/
theorem KR.olW {s : State} (h : KR (H := H) s₀ s) :
    s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s₀ 0 :=
  h.readW (R := argR s₀) (contains_pre (by decide)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.o_a.symm
    · exact hp.s_a.symm
    · exact hp.stk_a.symm)

end

/-! ## Facts about the offsets

Each proved once, by `omega` on `layout`, for the step proofs: an `omega`
over a step's context, which holds many facts about states and sizes, costs
far more. -/

theorem PSizes.B_ge (hz : PSizes H) : 64 ≤ H.P.B := by rcases hz.z.B with h | h <;> omega_using [h]
theorem PSizes.o_0_lt_S (hz : PSizes H) : 0 < H.S := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_B_1_lt_p31 (hz : PSizes H) : H.P.B + 1 < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_B_1_lt_p64 (hz : PSizes H) : H.P.B + 1 < 2 ^ 64 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_B_4_lt_p31 (hz : PSizes H) : H.P.B + 4 < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_B_lt_p31 (hz : PSizes H) : H.P.B < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_B_lt_p32 (hz : PSizes H) : H.P.B < 2 ^ 32 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_le_p64 (hz : PSizes H) : H.D ≤ 2 ^ 64 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_lt_p31 (hz : PSizes H) : H.D < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_lt_p32 (hz : PSizes H) : H.D < 2 ^ 32 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_D_lt_p64 (hz : PSizes H) : H.D < 2 ^ 64 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_S_lt_p31 (hz : PSizes H) : H.S < 2 ^ 31 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_W8_48_le_L (hz : PSizes H) : 8 * H.W + 48 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_W8_48_le_outO (hz : PSizes H) : 8 * H.W + 48 ≤ H.outO := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_L (hz : PSizes H) : 8 * H.W ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_using []
theorem PSizes.o_W8_le_hkO (hz : PSizes H) : 8 * H.W ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_intO (hz : PSizes H) : 8 * H.W ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_st0O (hz : PSizes H) : 8 * H.W ≤ H.st0O := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_st1O (hz : PSizes H) : 8 * H.W ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_stSO (hz : PSizes H) : 8 * H.W ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_stWO (hz : PSizes H) : 8 * H.W ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_sv (hz : PSizes H) : 8 * H.W ≤ H.sv := by
  simp only [Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_tO (hz : PSizes H) : 8 * H.W ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_W8_le_uO (hz : PSizes H) : 8 * H.W ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_cO_64d8_le_outO_16 (hz : PSizes H) : H.cO + 64 / 8 ≤ H.outO + 16 := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N4; omega_using []
theorem PSizes.o_cO_8_le_L (hz : PSizes H) : H.cO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.cO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_hkO_D_le_L (hz : PSizes H) : H.hkO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_hkO_lt_p31 (hz : PSizes H) : H.hkO < 2 ^ 31 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_intO_4_le_L (hz : PSizes H) : H.intO + 4 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_intO_lt_p31 (hz : PSizes H) : H.intO < 2 ^ 31 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_outO_16_le_L (hz : PSizes H) : H.outO + 16 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.outO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_outO_16_lt_p64 (hz : PSizes H) : H.outO + 16 < 2 ^ 64 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_outO_64d8_le_outO_16 (hz : PSizes H) : H.outO + 64 / 8 ≤ H.outO + 16 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N4; omega_using []
theorem PSizes.o_outO_8_le_L (hz : PSizes H) : H.outO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.outO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_outO_8_le_cO (hz : PSizes H) : H.outO + 8 ≤ H.cO := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_outO_le_cO (hz : PSizes H) : H.outO ≤ H.cO := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_2mS_le_L (hz : PSizes H) : H.st0O + 2 * H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_st0O_2mS_le_tO (hz : PSizes H) : H.st0O + 2 * H.S ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_3mS_le_L (hz : PSizes H) : H.st0O + 3 * H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_st0O_S_le_L (hz : PSizes H) : H.st0O + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_st0O_S_le_hkO (hz : PSizes H) : H.st0O + H.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_S_le_st0O_3mS (hz : PSizes H) : H.st0O + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_S_le_st1O (hz : PSizes H) : H.st0O + H.S ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_S_le_stSO (hz : PSizes H) : H.st0O + H.S ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_le_st0O (hz : PSizes H) : H.st0O ≤ H.st0O := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_le_st1O (hz : PSizes H) : H.st0O ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_le_stSO (hz : PSizes H) : H.st0O ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_lt_p31 (hz : PSizes H) : H.st0O < 2 ^ 31 := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_st1O_S_le_L (hz : PSizes H) : H.st1O + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_st1O_S_le_hkO (hz : PSizes H) : H.st1O + H.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st1O_S_le_st0O_3mS (hz : PSizes H) : H.st1O + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st1O_S_le_stSO (hz : PSizes H) : H.st1O + H.S ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st1O_S_le_stWO (hz : PSizes H) : H.st1O + H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st1O_S_le_uO (hz : PSizes H) : H.st1O + H.S ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st1O_lt_p31 (hz : PSizes H) : H.st1O < 2 ^ 31 := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_stSO_S_le_L (hz : PSizes H) : H.stSO + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_stSO_S_le_st0O_3mS (hz : PSizes H) : H.stSO + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stSO_S_le_stWO (hz : PSizes H) : H.stSO + H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stSO_hsS_le_L (hz : PSizes H) : H.stSO + H.stream.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stSO_lt_p31 (hz : PSizes H) : H.stSO < 2 ^ 31 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_stWO_S_le_L (hz : PSizes H) : H.stWO + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_stWO_S_le_intO (hz : PSizes H) : H.stWO + H.S ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stWO_S_le_uO (hz : PSizes H) : H.stWO + H.S ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stWO_hsS_le_L (hz : PSizes H) : H.stWO + H.stream.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stWO_hsS_le_hkO (hz : PSizes H) : H.stWO + H.stream.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stWO_hsS_le_intO (hz : PSizes H) : H.stWO + H.stream.S ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega_arith
theorem PSizes.o_stWO_le_intO (hz : PSizes H) : H.stWO ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stWO_le_tO (hz : PSizes H) : H.stWO ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_stWO_lt_p31 (hz : PSizes H) : H.stWO < 2 ^ 31 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_sv_64_le_L (hz : PSizes H) : H.sv + 64 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_tO_D_le_L (hz : PSizes H) : H.tO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_tO_lt_p31 (hz : PSizes H) : H.tO < 2 ^ 31 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_uO_D_le_L (hz : PSizes H) : H.uO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_uO_D_le_tO (hz : PSizes H) : H.uO + H.D ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_uO_lt_p31 (hz : PSizes H) : H.uO < 2 ^ 31 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega_arith
theorem PSizes.o_so_48_le_L (hz : PSizes H) : H.P.so + 48 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; have := hz.z.fits; omega_arith
theorem PSizes.o_so_48_le_W8 (hz : PSizes H) : H.P.so + 48 ≤ 8 * H.W := by
  have := hz.z.D.2.1; have := hz.z.fits; omega_arith
theorem PSizes.o_stWO_le_uO (hz : PSizes H) : H.stWO ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_S_eq_st1O (_hz : PSizes H) : H.st0O + H.S = H.st1O := rfl
theorem PSizes.o_st0O_le_stWO (hz : PSizes H) : H.st0O ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_hkO_N_le_L (hz : PSizes H) : H.hkO + H.P.N ≤ (H.W + H.S) * 8 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_st0O_le_hkO (hz : PSizes H) : H.st0O ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_D_le_B (hz : PSizes H) : H.D ≤ H.P.B := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith
theorem PSizes.o_sv_64_le_stWO (hz : PSizes H) : H.sv + 64 ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_st0O_3mS_le_stWO (hz : PSizes H) : H.st0O + 3 * H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega_using []
theorem PSizes.o_B_5_le_L (hz : PSizes H) : H.P.B + 5 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega_arith

end VG.Proof.Pbkdf2.Md.X86_64.Pbk

end

end


/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`, correct

`pbkdf2` saves our caller's registers, makes the key (hashing a password
longer than a block), HMAC's states for it and the inner state after the salt;
then each block `i` of the output is `U₁` (`update` with `INT (i)` and HMAC's
`finalize`), `iterate` from it, and as much of `T_i` as the output still
needs.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK ea_nat wp_mov32r zx32 contains_pre)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG After SavedRegs SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep readW_writeW_ne InRegions.right' sub_of_off sub_of_self bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep bytesAt_getD' writeBytes_at xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-! ## The entry -/

omit hp hz in
/-- After `scratch` is loaded. -/
structure Loaded (s₀ s : State) : Prop where
  r8 : s.gpr .r8 = scr s₀
  r10 : s.gpr .r10 = s₀.gpr .r8
  other : ∀ r, r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

omit hz in
theorem loadScr_ok : WP isa (.block Hash.loadScr) s₀ (Loaded s₀) := by
  simp only [Hash.loadScr]
  refine wp_mov fun s₁ u₁ _ _ => ?_
  refine wp_movm (a := s₀.gpr .rsp + BitVec.ofNat 64 16) (by rw [ea_nat, u₁.other _ (by decide)]) ?_
    fun s₂ u₂ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁.rd, u₁.wr, hp.rd]
    exact ⟨argR s₀, by simp, show (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Contains _ 8 from
      Offset.contains _ (by decide) (by decide) (by decide)⟩
  · rw [u₂.gpr, u₁.mem]; rfl
  · rw [u₂.other _ (by decide), u₁.gpr]
  · intro r h₁ h₂; rw [u₂.other r h₁, u₁.other r h₂]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

theorem entry_ok {s₂ : State} (hl₂ : Loaded s₀ s₂) : WP isa (.block H.entry) s₂ fun s => KR (H := H) s₀ s ∧
    s.gpr .rbx = pw s₀ ∧ s.gpr .rbp = s₀.gpr .rsi ∧ s.gpr .r12 = salt s₀ ∧ s.gpr .r13 = s₀.gpr .rcx ∧
    s.cf = some (decide (pwl s₀ < H.P.B + 1)) := by
  have hW := hz.W
  have := hp.snw; have hc0 := hp.c0
  have hS : H.S = H.P.N + H.P.B := rfl
  simp only [Hash.entry]
  have h8 : s₂.gpr .r8 = scr s₀ := hl₂.r8
  have g₂ : ∀ r, r ≠ .r8 → r ≠ .r10 → s₂.gpr r = s₀.gpr r := hl₂.other
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.save_ok H.hh h8 hW (L := (H.W + H.S) * 8)
    (by rw [hl₂.wr]; exact sc_mem hp) (by show 8 * H.W + 48 ≤ (H.W + H.S) * 8; exact hz.o_W8_48_le_L)
    fun s₃ g₃ rd₃ wr₃ f₃ sv₃ => ?_
  refine wp_mov fun s₄ u₄ _ _ => ?_
  obtain h15 : s₄.gpr .r15 = scr s₀ := by rw [u₄.gpr, g₃, h8]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, wr₃, hl₂.wr]
  refine wp_store (a := A s₀ H.outO) (by rw [ea_nat, h15]) (in_sc hp hz wr₄ (by exact hz.o_outO_8_le_L))
    fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_mov32r fun s₆ u₆ => wp_subi fun s₇ u₇ _ => ?_
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, wr₅, wr₄]
  obtain h15' : s₆.gpr .r15 = scr s₀ := by rw [u₆.other _ (by decide), g₅, h15]
  refine wp_store (a := A s₀ H.cO) (by rw [ea_nat, u₇.other _ (by decide), h15'])
    (by rw [u₇.wr, wr₆]; exact in_sc hp hz rfl (by exact hz.o_cO_8_le_L)) fun s₈ g₈ m₈ rd₈ wr₈ => ?_
  refine wp_mov fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ => wp_mov fun s₁₁ u₁₁ _ _ =>
    wp_mov fun s₁₂ u₁₂ _ _ => wp_cmpi fun s₁₃ g₁₃ m₁₃ rd₁₃ wr₁₃ c₁₃ _ => WP.block_nil ?_
  -- The registers.
  obtain g : ∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r8 → r ≠ .r10 →
      s₁₃.gpr r = s₀.gpr r := fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => by
    rw [g₁₃, u₁₂.other r h₆, u₁₁.other r h₅, u₁₀.other r h₄, u₉.other r h₃, g₈, u₇.other r h₁, u₆.other r h₁,
      g₅, u₄.other r h₂, g₃, g₂ r h₇ h₈]
  obtain gs : ∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → s₈.gpr r = s₂.gpr r :=
    fun r h₁ h₂ _ _ _ _ => by rw [g₈, u₇.other r h₁, u₆.other r h₁, g₅, u₄.other r h₂, g₃]
  obtain rax₈ : s₇.gpr .rax = BitVec.ofNat 64 (cc s₀ - 1) := by
    rw [u₇.gpr, u₆.gpr, g₅, u₄.other _ (by decide), g₃, hl₂.r10, zx32, sx1,
      ofNat_pred hc0]
  obtain r9₄ : s₄.gpr .r9 = out s₀ := by rw [u₄.other _ (by decide), g₃, g₂ _ (by decide) (by decide)]
  -- The memory.
  obtain m₁₃ : s₁₃.mem = (s₃.mem.writeW (A s₀ H.outO) (out s₀)).writeW (A s₀ H.cO)
      (BitVec.ofNat 64 (cc s₀ - 1)) := by
    rw [m₁₃, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈, u₇.mem, u₆.mem, m₅, u₄.mem, r9₄, rax₈]
  obtain dOC : Region.Disjoint ⟨A s₀ H.outO, 8⟩ ⟨A s₀ H.cO, 8⟩ := part_disj hz (Or.inl (by exact hz.o_outO_8_le_cO)) (by exact hz.o_outO_8_le_L) (by exact hz.o_cO_8_le_L)
  obtain fW : Frame [sR s₀ H.outO 16] s₃.mem s₁₃.mem := by
    rw [m₁₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl _) (by exact hz.o_outO_64d8_le_outO_16)
      (by exact hz.o_outO_16_lt_p64))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by exact hz.o_outO_le_cO) (by exact hz.o_cO_64d8_le_outO_16) (by exact hz.o_outO_16_lt_p64))
  obtain f₀ : Frame [outR s₀, scR (H := H) s₀, stkR s₀] s₀.mem s₁₃.mem := by
    have e₂ : s₂.mem = s₀.mem := hl₂.mem
    rw [← e₂]
    refine (f₃.sub fun r hr => ?_).trans (fW.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR (H := H) s₀, by simp, Offset.sub_base _ (by show 8 * H.W + 48 ≤ (H.W + H.S) * 8; exact hz.o_W8_48_le_L)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR (H := H) s₀, by simp, part_sub (by exact hz.o_outO_16_le_L)⟩
  obtain sv : SavedRegs H.hh (scr s₀) s₀ s₃.mem :=
    ⟨by rw [sv₃.rbx, g₂ _ (by decide) (by decide)], by rw [sv₃.rbp, g₂ _ (by decide) (by decide)],
      by rw [sv₃.r12, g₂ _ (by decide) (by decide)], by rw [sv₃.r13, g₂ _ (by decide) (by decide)],
      by rw [sv₃.r14, g₂ _ (by decide) (by decide)], by rw [sv₃.r15, g₂ _ (by decide) (by decide)]⟩
  refine ⟨⟨by rw [rd₁₃, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, rd₈, u₇.rd, u₆.rd, rd₅, u₄.rd, rd₃, hl₂.rd],
    by rw [wr₁₃, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, wr₈, u₇.wr, wr₆],
    g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), g₈, u₇.other _ (by decide), h15'],
    SavedRegs.frame H.hh sv fW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (a := 8 * H.W) (m := 48) (Or.inl (by exact hz.o_W8_48_le_outO)) (by exact hz.o_W8_48_le_L) (by exact hz.o_outO_16_le_L),
    by rw [m₁₃, readW_writeW_ne _ _ dOC, Mem.readW_writeW_self64],
    by rw [m₁₃, Mem.readW_writeW_self64], f₀⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [c₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide), sx_ofNat (by exact hz.o_B_1_lt_p31), toNat_ofNat_lt (by exact hz.o_B_1_lt_p64)]

/-! ## Helpers -/

omit hp hz in
theorem KR.same {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) (hm : s'.mem = s.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp h15 (rs := []) (hm ▸ Frame.refl [] s.mem) (fun _ h => by simp at h) (fun _ h => by simp at h)

omit hp hz in
theorem KR.upd {s s' : State} (h : KR (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ≠ .r15 ∧ d ≠ .rsp) : KR (H := H) s₀ s' :=
  h.same u.rd u.wr (u.other _ hd.2.symm) (u.other _ hd.1.symm) u.mem

omit hp hz in
/-- `d ← scratch + o`. -/
theorem scr_ok {s : State} {d : Reg} (h15 : s.gpr .r15 = scr s₀) {o : Nat} (ho : o < 2 ^ 31)
    {rest : List Instr} {Q : State → Prop} (k : ∀ s', Upd s s' d (A s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr d o ++ rest)) s Q := by
  simp only [VG.Impl.Pbkdf2.Md.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_addi fun s₂ u₂ => k s₂ ⟨?_, fun r hr => by rw [u₂.other r hr, u₁.other r hr],
    by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  rw [u₂.gpr, u₁.gpr, h15, sx_ofNat ho]

omit hp hz in
theorem stk_sub {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ 24) :
    Region.Sub (below (s.gpr .rsp) n) (stkR s₀) := by
  rw [h.rsp]; exact below_stk hn

omit hz in
theorem stk_sc {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ 24) {R : Region}
    (hR : Region.Sub R (scR (H := H) s₀)) : (below (s.gpr .rsp) n).Disjoint R :=
  (hp.stk_s.sub_left (stk_sub h hn)).sub_right hR

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

/-! ## The key -/

/-- The key HMAC's `init` gets: the password, or the digest of a password
longer than a block, in `scratch`; either gives the same `K₀`. -/
structure KeyAt (hH : HashOK H) (s₀ : State) (m : Mem) (kp : Addr) (kl : Nat) : Prop where
  loc : (kp = pw s₀ ∧ kl = pwl s₀) ∨ (kp = A s₀ H.hkO ∧ kl = H.D)
  le : kl ≤ H.P.B
  k0 : blockKey hH.SH.H (bytesAt m kp kl) = blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

omit hp hz in
theorem hash_len (hH : HashOK H) (m : List Byte) : (hH.SH.H.hash m).length = H.D := by
  rw [hH.hash, List.length_take, VG.Proof.MdStream.Md.hash, hH.md.digest_length]; have := hH.hDN; omega_arith

omit hp hz in
/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash (hH : HashOK H) {k : List Byte} (hk : H.P.B < k.length) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  obtain hl := hash_len hH k; have hB := hH.hB; have := hH.hDL
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ H.P.B < H.D by omega_arith))]

omit hp hz in
theorem blockKey_length (hH : HashOK H) (k : List Byte) : (blockKey hH.SH.H k).length = H.P.B := by
  obtain hB := hH.hB; have := hH.hDL
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [hash_len]; omega_arith
  · omega_arith

omit hp hz in
/-- What the entry sets up, kept until the salt is absorbed. -/
structure KE (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  rbx : s.gpr .rbx = pw s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = salt s₀
  r13 : s.gpr .r13 = s₀.gpr .rcx

/-- The registers `KE` fixes. -/
abbrev eregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

omit hp hz in
theorem KE.upd {s s' : State} (h : KE (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ eregs) : KE (H := H) s₀ s' := by
  obtain ne : ∀ r ∈ eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u ⟨(ne _ (by simp)).symm, (ne _ (by simp)).symm⟩, by rw [u.other _ (ne _ (by simp)), h.rbx],
    by rw [u.other _ (ne _ (by simp)), h.rbp], by rw [u.other _ (ne _ (by simp)), h.r12],
    by rw [u.other _ (ne _ (by simp)), h.r13]⟩

theorem KE.call {s s' : State} (h : KE (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {ws : List Region} {n : Nat} (hn : n ≤ 24)
    (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) : KE (H := H) s₀ s' :=
  ⟨h.kr.call hp hz hrd hwr hcs hn hf hw, by rw [hcs _ (by simp [calleeSaved]), h.rbx],
    by rw [hcs _ (by simp [calleeSaved]), h.rbp], by rw [hcs _ (by simp [calleeSaved]), h.r12],
    by rw [hcs _ (by simp [calleeSaved]), h.r13]⟩

/-! ### Hashing a password longer than a block -/

omit hp in
theorem hk1_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO)) s fun t =>
      KE (H := H) s₀ t ∧ t.gpr .rdi = A s₀ H.stWO := by
  have hB := hz.z.B_le
  have hD := hz.z.D
  rw [← List.append_nil (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO)]
  exact scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), u₁.gpr⟩

theorem hk2_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hdi : s.gpr .rdi = A s₀ H.stWO) :
    WP isa (.call H.initN H.initC) s fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  exact VG.Proof.Pbkdf2.Md.X86_64.Calls.init_call hH.stream (st := A s₀ H.stWO) hdi
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by exact hz.o_stWO_hsS_le_L))
    (stk_sc hp h.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))) fun s₂ a₂ r₂ =>
      ⟨h.call hp hz a₂.rd a₂.wr a₂.cs (by decide) a₂.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩, r₂⟩

/-- `update`'s arguments: the password. -/
theorem hk3_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO ++ ([.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbx),
      .mov .rcx (.reg .rbp), .mov .r8 (.reg .r15)] : List Instr))) s fun t => KE (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream t (A s₀ H.stWO) (pw s₀) (scr s₀) (pwl s₀) ∧
      t.gpr .rsi = BitVec.ofNat 64 0 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₃ u₃ => wp_mov32i fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ => WP.block_nil ?_
  obtain k₇ := ((((h.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇
    (by decide)
  refine ⟨k₇, ?_, by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl,
    by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact hr⟩
  exact
    { rdi := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.gpr]
      rdx := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
          u₃.other _ (by decide), h.rbx]
      rcx := by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.rbp]
      r8 := by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.kr.r15]
      cd := VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [k₇.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₇.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_low hp k₇.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      d_st := hp.pw_s.sub_right (part_sub (by exact hz.o_stWO_hsS_le_L))
      d_sc := hp.pw_s.sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L))
      stk_st := stk_sc hp k₇.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_d := (hp.stk_pw.sub_left (stk_sub k₇.kr (by decide)))
      stk_sc := stk_sc hp k₇.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }

theorem hk4_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (ua : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s (A s₀ H.stWO) (pw s₀) (scr s₀) (pwl s₀))
    (hsi : s.gpr .rsi = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.call H.updN H.updC) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_call hH.stream ua (by have := hp.pwnw; omega_arith) fun s₈ a₈ r₈ =>
    ⟨h.call hp hz a₈.rd a₈.wr a₈.cs (by decide) a₈.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  · have := r₈ [] hr hsi
    rwa [List.nil_append, h.kr.pwBytes hp] at this

/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO ++ ([.mov .rsi (.reg .rbp)] : List Instr) ++
      VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.hkO ++ ([.mov .rcx (.reg .r15)] : List Instr))) s fun t =>
      KE (H := H) s₀ t ∧ VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH.stream t (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀) ∧
      t.gpr .rsi = s₀.gpr .rsi ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  simp only [List.append_assoc]
  refine scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ _ _ => ?_
  refine scr_ok (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), h.kr.r15]) (by exact hz.o_hkO_lt_p31)
    fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ _ _ => WP.block_nil ?_
  obtain k₁₂ := (((h.upd u₉ (by decide)).upd u₁₀ (by decide)).upd u₁₁ (by decide)).upd u₁₂ (by decide)
  refine ⟨k₁₂, ?_, by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
    h.rbp], by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]; exact hr⟩
  exact
    { rdi := by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr]
      rdx := by rw [u₁₂.other _ (by decide), u₁₁.gpr]
      rcx := by rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), h.kr.r15]
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₁₂.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_part hp k₁₂.kr (by rw [hF]; exact hz.o_hkO_N_le_L)
        · exact cov_low hp k₁₂.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_o := part_disj hz (Or.inl (by exact hz.o_stWO_hsS_le_hkO)) (by exact hz.o_stWO_hsS_le_L) (by rw [hF]; exact hz.o_hkO_N_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      o_sc := (low_disj hz (by exact hz.o_W8_le_hkO) (by rw [hF]; exact hz.o_hkO_N_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      stk_st := stk_sc hp k₁₂.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_o := stk_sc hp k₁₂.kr (by decide) (part_sub (by rw [hF]; exact hz.o_hkO_N_le_L))
      stk_sc := stk_sc hp k₁₂.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }

theorem hk6_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (fa : VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH.stream s (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀))
    (hsi : s.gpr .rsi = s₀.gpr .rsi) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.call H.finN H.finC) s fun t => KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.fin_call hH.stream fa fun s₁₃ a₁₃ r₁₃ =>
    ⟨h.call hp hz a₁₃.rd a₁₃.wr a₁₃.cs (by decide) a₁₃.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_hkO, by rw [hF]; exact hz.o_hkO_N_le_L⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  · rw [bytesAt_take _ _ hD.2.1]
    exact r₁₃ _ hr (by rw [bytesAt_length]; exact (s₀.gpr .rsi).isLt)
      (by rw [hsi, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp in
theorem hk7_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.hkO ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.D))] : List Instr))) s fun t =>
      KE (H := H) s₀ t ∧ t.gpr .rdx = A s₀ H.hkO ∧ (t.gpr .rcx).toNat = H.D ∧ t.mem = s.mem := by
  obtain hD := hz.z.D; have hN := hz.z.N
  have hB := hz.z.B_le
  refine scr_ok h.kr.r15 (by exact hz.o_hkO_lt_p31) fun s₁₄ u₁₄ => wp_mov32i fun s₁₅ u₁₅ _ _ => WP.block_nil ?_
  exact ⟨(h.upd u₁₄ (by decide)).upd u₁₅ (by decide), by rw [u₁₅.other _ (by decide), u₁₄.gpr],
    by rw [u₁₅.gpr, zx_ofNat (by exact hz.o_D_lt_p32), toNat_ofNat_lt (by exact hz.o_D_lt_p64)], by rw [u₁₅.mem, u₁₄.mem]⟩

theorem hashKey_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) :
    WP isa H.hashKey s fun t => KE (H := H) s₀ t ∧ t.gpr .rdx = A s₀ H.hkO ∧ (t.gpr .rcx).toNat = H.D ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (hk1_ok hz h) fun s₁ ⟨k₁, d₁⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hp hz hH k₂ r₂) fun s₃ ⟨k₃, a₃, i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok hp hz hH k₄ r₄) fun s₅ ⟨k₅, a₅, i₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok hz k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

omit hp hz in
/-- Where the key is, and its length. -/
abbrev kp (H : Hash) (s₀ : State) : Addr := if pwl s₀ < H.P.B + 1 then pw s₀ else A s₀ H.hkO
omit hp hz in
abbrev kl (H : Hash) (s₀ : State) : Nat := if pwl s₀ < H.P.B + 1 then pwl s₀ else H.D

theorem key_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (hcf : s.cf = some (decide (pwl s₀ < H.P.B + 1))) :
    WP isa H.key s fun t => KE (H := H) s₀ t ∧ t.gpr .rdx = kp H s₀ ∧ (t.gpr .rcx).toNat = kl H s₀ ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hD := hz.z.D
  unfold Hash.key
  refine WP.ite (!decide (pwl s₀ < H.P.B + 1)) (by simp [eval, hcf]) (fun hT => ?_) fun hF => ?_
  · have hlong : ¬ pwl s₀ < H.P.B + 1 := of_decide_eq_false (Bool.not_eq_true' _ ▸ hT)
    obtain e₁ : kp H s₀ = A s₀ H.hkO := ite_eq_right_of_eq_false _ _ (eq_false hlong)
    obtain e₂ : kl H s₀ = H.D := ite_eq_right_of_eq_false _ _ (eq_false hlong)
    rw [e₁, e₂]
    refine WP.mono (hashKey_ok hp hz hH h) fun t ⟨k, rdx, rcx, hb⟩ =>
      ⟨k, rdx, rcx, ⟨.inr ⟨rfl, rfl⟩, by exact hz.o_D_le_B, ?_⟩⟩
    rw [hb, blockKey_hash hH (by rw [bytesAt_length]; omega_arith)]
  · have hshort : pwl s₀ < H.P.B + 1 := of_decide_eq_true (by simpa using hF)
    obtain e₁ : kp H s₀ = pw s₀ := ite_eq_left_of_eq_true _ _ (eq_true hshort)
    obtain e₂ : kl H s₀ = pwl s₀ := ite_eq_left_of_eq_true _ _ (eq_true hshort)
    rw [e₁, e₂]
    refine wp_mov fun t₁ u₁ _ _ => wp_mov fun t₂ u₂ _ _ => WP.block_nil ?_
    refine ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.rbx],
      by rw [u₂.gpr, u₁.other _ (by decide), h.rbp], ⟨.inl ⟨rfl, rfl⟩, by omega_arith, ?_⟩⟩
    rw [u₂.mem, u₁.mem, h.kr.pwBytes hp]

/-! ## HMAC's states -/

omit hp hz in
theorem repr_keep (hH : HashOK H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.stream.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd
    (by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 2 ^ 64; omega_arith) hi) hr

omit hp hz in
/-- A state copied from `p` to `q` represents the same message. -/
theorem repr_copy (hH : HashOK H) {m : Mem} {p q : Addr} {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr (writeBytes m q (bytesAt m p H.S)) q msg := by
  have : H.S ≤ 256 := by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 256; omega_arith
  refine hH.stream.repr _ _ _ _ _ (fun i hi => ?_) hr
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_arith),
    bytesAt_getD' _ _ (show i < H.S from hi)]

/-- `K₀`, the password as a key. -/
abbrev K0 (hH : HashOK H) (s₀ : State) : List Byte := blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- HMAC's states in `scratch`: `K₀ ⊕ ipad`, `K₀ ⊕ opad`, and `K₀ ⊕ ipad`
after the salt. -/
structure States (hH : HashOK H) (s₀ : State) (m : Mem) : Prop where
  i : hH.SH.Repr m (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad)
  o : hH.SH.Repr m (A s₀ H.st1O) (xorPad (K0 hH s₀) opad)
  s : hH.SH.Repr m (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad ++ bytesAt s₀.mem (salt s₀) (sl s₀))

omit hp in
theorem States.keep (hH : HashOK H) {m m' : Mem} (h : States hH s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ H.st0O (3 * H.S)) r) : States hH s₀ m' := by
  exact ⟨repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by exact hz.o_st0O_S_le_st0O_3mS))) h.i,
    repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by exact hz.o_st0O_le_st1O) (by exact hz.o_st1O_S_le_st0O_3mS))) h.o,
    repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by exact hz.o_st0O_le_stSO) (by exact hz.o_stSO_S_le_st0O_3mS))) h.s⟩

omit hz in
/-- Regions a call writes, disjoint from a part of `scratch`. -/
theorem disj_call {s : State} (h : KR (H := H) s₀ s) {X : Region} (hX : Region.Sub X (scR (H := H) s₀))
    {ws : List Region} {n : Nat} (hn : n ≤ 24) (hw : ∀ r ∈ ws, X.Disjoint r) :
    ∀ r ∈ ws ++ [below (s.gpr .rsp) n], X.Disjoint r := fun r hr => by
  rcases List.mem_append.mp hr with hr | hr
  · exact hw r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact (stk_sc hp h hn hX).symm

/-- The key's region: where HMAC's `init` may read it. -/
theorem KeyAt.facts (hH : HashOK H) {m : Mem} {kp : Addr} {kl : Nat} (hk : KeyAt hH s₀ m kp kl) {s : State}
    (h : KR (H := H) s₀ s) :
    Covers [⟨kp, kl⟩] (s.rd ++ s.wr) ∧ Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st0O, H.S⟩ ∧
      Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st1O, H.S⟩ ∧ Region.Disjoint ⟨kp, kl⟩ (lowR (H := H) s₀) ∧
      (below (s.gpr .rsp) 24).Disjoint ⟨kp, kl⟩ := by
  obtain hD := hz.z.D; have hN := hz.z.N
  rcases hk.loc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [h.rd, hp.rd]; simp)),
      hp.pw_s.sub_right (part_sub (by exact hz.o_st0O_S_le_L)), hp.pw_s.sub_right (part_sub (by exact hz.o_st1O_S_le_L)),
      hp.pw_s.sub_right low_sub, hp.stk_pw.sub_left (stk_sub h (Nat.le_refl _))⟩
  · refine ⟨Covers.of_sub fun r hr => ?_, part_disj hz (Or.inr (by exact hz.o_st0O_S_le_hkO)) (by exact hz.o_hkO_D_le_L) (by exact hz.o_st0O_S_le_L),
      part_disj hz (Or.inr (by exact hz.o_st1O_S_le_hkO)) (by exact hz.o_hkO_D_le_L) (by exact hz.o_st1O_S_le_L), low_disj hz (by exact hz.o_W8_le_hkO) (by exact hz.o_hkO_D_le_L),
      stk_sc hp h (Nat.le_refl _) (part_sub (by exact hz.o_hkO_D_le_L))⟩
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨r', h', off, e, l⟩ := cov_part hp h (o := H.hkO) (n := H.D) (by exact hz.o_hkO_D_le_L)
    exact ⟨r', List.mem_append_right _ h', off, e, l⟩

/-- HMAC's `init`'s arguments: its two states and the key. -/
theorem su1_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hdx : s.gpr .rdx = kp H s₀)
    (hcx : (s.gpr .rcx).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.st0O ++ VG.Impl.Pbkdf2.Md.X86_64.scr .rsi H.st1O ++
      ([.mov .r8 (.reg .r15)] : List Instr))) s fun t => KE (H := H) s₀ t ∧
      InitArgs (H := H) t (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀) ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  simp only [List.append_assoc]
  refine scr_ok h.kr.r15 (by exact hz.o_st0O_lt_p31) fun s₁ u₁ => ?_
  refine scr_ok (by rw [u₁.other _ (by decide), h.kr.r15]) (by exact hz.o_st1O_lt_p31) fun s₂ u₂ => wp_mov fun s₃ u₃ _ _ =>
    WP.block_nil ?_
  obtain k₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain ⟨kc, k_i, k_o, k_s, k_stk⟩ := hk.facts hp hz hH k₃.kr
  refine ⟨k₃, ?_, m₃ ▸ hk⟩
  exact
    { rdi := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      rsi := by rw [u₃.other _ (by decide), u₂.gpr]
      rdx := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdx]
      rcx := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hcx]
      r8 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.r15]
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
      stk_i := stk_sc hp k₃.kr (Nat.le_refl _) (part_sub (by exact hz.o_st0O_S_le_L))
      stk_o := stk_sc hp k₃.kr (Nat.le_refl _) (part_sub (by exact hz.o_st1O_S_le_L))
      stk_k := k_stk
      stk_s := stk_sc hp k₃.kr (Nat.le_refl _) low_sub
      scnw := by show (scr s₀).toNat + 8 * H.W ≤ 2 ^ 64; omega_arith }

/-- HMAC's `init`: the key's inner and outer states. -/
theorem su2_ok (hH : HashOK H) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) {s : State} (h : KE (H := H) s₀ s)
    (ia : InitArgs (H := H) s (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀))
    (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.call H.hmacInitN H.hmacInit) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine hinit_call hH hI hIsp hId ia fun s₄ rd₄ wr₄ cs₄ f₄ ri₄ ro₄ => ⟨?_, ?_, ?_⟩
  · exact h.call hp hz rd₄ wr₄ cs₄ (Nat.le_refl _) f₄ fun r hr => by
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
    WP isa (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.st0O .r15 H.stSO H.S)
      (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stSO ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 H.P.B)),
        .mov .rdx (.reg .r12), .mov .rcx (.reg .r13), .mov .r8 (.reg .r15)] : List Instr)))) s₄ fun t =>
      KE (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream t (A s₀ H.stSO) (salt s₀) (scr s₀) (sl s₀) ∧
      t.gpr .rsi = BitVec.ofNat 64 H.P.B ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad) ∧
      hH.SH.Repr t.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.copy_ok (src := .r15) (dst := .r15) (by decide) (by decide)
    (so := H.st0O) (d := H.stSO) (n := H.S) (by exact hz.o_0_lt_S) (by exact hz.o_S_lt_p31) (s := s₄)
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_st0O_S_le_L])))
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_stSO_S_le_L]))
    (by rw [h.kr.r15]; exact part_disj hz (Or.inl (by exact hz.o_st0O_S_le_stSO)) (by exact hz.o_st0O_S_le_L) (by exact hz.o_stSO_S_le_L))) fun s₅ c₅ => ?_)
  rw [h.kr.r15] at c₅
  obtain f₅ : Frame [sR s₀ H.stSO H.S] s₄.mem s₅.mem := by
    rw [c₅.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain k₅ : KE (H := H) s₀ s₅ := ⟨h.kr.write hz c₅.rd c₅.wr (c₅.other _ (by decide) (by decide))
      (c₅.other _ (by decide) (by decide)) (o := H.stSO) (n := H.S) (by exact hz.o_st0O_le_stSO) (by exact hz.o_stSO_S_le_L) f₅,
    by rw [c₅.other _ (by decide) (by decide), h.rbx], by rw [c₅.other _ (by decide) (by decide), h.rbp],
    by rw [c₅.other _ (by decide) (by decide), h.r12], by rw [c₅.other _ (by decide) (by decide), h.r13]⟩
  obtain dS : ∀ o, o + H.S ≤ H.stSO → ∀ r ∈ [sR s₀ H.stSO H.S], Region.Disjoint ⟨A s₀ o, H.S⟩ r := fun o ho r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl ho) (by omega_using [ho, hz.o_stSO_S_le_L]) (by exact hz.o_stSO_S_le_L)
  obtain ri₅ := repr_keep hH f₅ (dS _ (by exact hz.o_st0O_S_le_stSO)) ri₄
  obtain ro₅ := repr_keep hH f₅ (dS _ (by exact hz.o_st1O_S_le_stSO)) ro₄
  obtain rs₅ : hH.SH.Repr s₅.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad) := by rw [c₅.mem]; exact repr_copy hH ri₄
  refine scr_ok k₅.kr.r15 (by exact hz.o_stSO_lt_p31) fun s₆ u₆ => wp_mov32i fun s₇ u₇ _ _ => wp_mov fun s₈ u₈ _ _ =>
    wp_mov fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ => WP.block_nil ?_
  obtain k₁₀ := ((((k₅.upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀
    (by decide)
  obtain m₁₀ : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  refine ⟨k₁₀, ?_, by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      zx_ofNat (by exact hz.o_B_lt_p32)], m₁₀ ▸ ri₅, m₁₀ ▸ ro₅, m₁₀ ▸ rs₅⟩
  exact
    { rdi := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
          u₇.other _ (by decide), u₆.gpr]
      rdx := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.r12]
      rcx := by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.r13]
      r8 := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.kr.r15]
      cd := VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [k₁₀.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₁₀.kr (by exact hz.o_stSO_hsS_le_L)
        · exact cov_low hp k₁₀.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stSO) (by exact hz.o_stSO_hsS_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      d_st := hp.sa_s.sub_right (part_sub (by exact hz.o_stSO_hsS_le_L))
      d_sc := hp.sa_s.sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L))
      stk_st := stk_sc hp k₁₀.kr (by decide) (part_sub (by exact hz.o_stSO_hsS_le_L))
      stk_d := hp.stk_sa.sub_left (stk_sub k₁₀.kr (by decide))
      stk_sc := stk_sc hp k₁₀.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }

/-- `update` with the salt. -/
theorem su4_ok (hH : HashOK H) {s₁₀ : State} (k₁₀ : KE (H := H) s₀ s₁₀)
    (ua : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s₁₀ (A s₀ H.stSO) (salt s₀) (scr s₀) (sl s₀))
    (hsi : s₁₀.gpr .rsi = BitVec.ofNat 64 H.P.B)
    (ri : hH.SH.Repr s₁₀.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad))
    (ro : hH.SH.Repr s₁₀.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad))
    (rs : hH.SH.Repr s₁₀.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad)) :
    WP isa (.call H.updN H.updC) s₁₀ fun t => KE (H := H) s₀ t ∧ States hH s₀ t.mem := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_call hH.stream ua (by have := hp.sanw; omega_arith) fun s₁₁ a₁₁ r₁₁ => ?_
  obtain k₁₁ := k₁₀.call hp hz a₁₁.rd a₁₁.wr a₁₁.cs (by decide) a₁₁.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stSO, by exact hz.o_stSO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  obtain dW : ∀ o, H.st0O ≤ o → o + H.S ≤ H.stSO → ∀ r ∈ [(⟨A s₀ H.stSO, H.stream.S⟩ : Region), ⟨scr s₀, hH.stream.Wb⟩] ++
      [below (s₁₀.gpr .rsp) 16], Region.Disjoint ⟨A s₀ o, H.S⟩ r := fun o ho₀ ho =>
    disj_call hp k₁₀.kr (part_sub (by omega_using [ho, hz.o_stSO_S_le_L])) (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact part_disj hz (Or.inl ho) (by omega_using [ho, hz.o_stSO_S_le_L]) (by exact hz.o_stSO_hsS_le_L)
      · exact (low_disj hz (by omega_using [ho₀, hz.o_W8_le_st0O]) (by omega_using [ho, hz.o_stSO_S_le_L])).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
  refine ⟨k₁₁, repr_keep hH a₁₁.frame (dW _ (by exact hz.o_st0O_le_st0O) (by exact hz.o_st0O_S_le_stSO)) ri,
    repr_keep hH a₁₁.frame (dW _ (by exact hz.o_st0O_le_st1O) (by exact hz.o_st1O_S_le_stSO)) ro, ?_⟩
  have := r₁₁ _ rs (by rw [hsi, xorPad_length, blockKey_length])
  rwa [k₁₀.kr.saltBytes hp] at this

theorem setup_ok (hH : HashOK H) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) {s : State} (h : KE (H := H) s₀ s)
    (hdx : s.gpr .rdx = kp H s₀) (hcx : (s.gpr .rcx).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa H.setup s fun t => KE (H := H) s₀ t ∧ States hH s₀ t.mem := by
  unfold Hash.setup
  refine WP.seq (WP.mono (su1_ok hp hz hH h hdx hcx hk) fun s₁ ⟨k₁, a₁, h₁⟩ => ?_)
  refine WP.seq (WP.mono (su2_ok hp hz hH hI hIsp hId k₁ a₁ h₁) fun s₂ ⟨k₂, i₂, o₂⟩ => ?_)
  refine WP.assoc (WP.seq (WP.mono (su3_ok hp hz hH k₂ i₂ o₂) fun s₃ ⟨k₃, a₃, si₃, i₃, o₃, r₃⟩ => ?_))
  exact su4_ok hp hz hH k₃ a₃ si₃ i₃ o₃ r₃

end

end VG.Proof.Pbkdf2.Md.X86_64.Pbk

end

end

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`'s loop

After `k` blocks of the output (`Inv`), `out` holds the first `min (k D)
out_len` bytes of `T₁ ‖ … ‖ T_k`; a step computes `T_{k+1}` (`U₁` by `update`
with `INT (k + 1)` and HMAC's `finalize`, then `iterate`) and copies as much
of it as the output still needs.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK ea_nat wp_mov32r zx32 contains_pre)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG After SavedRegs SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep readW_writeW_ne InRegions.right' sub_of_off sub_of_self bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep bytesAt_getD' writeBytes_at xorPad_length)
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

/-- After `k` blocks of the output. -/
structure Inv (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR (H := H) s₀ s
  st : States hH s₀ s.mem
  rbx : s.gpr .rbx = BitVec.ofNat 64 (k + 1)
  rbp : s.gpr .rbp = s₀.gpr .rcx
  r12 : s.gpr .r12 = BitVec.ofNat 64 (ol s₀ - done H s₀ k)
  r13 : s.gpr .r13 = out s₀ + BitVec.ofNat 64 (done H s₀ k)
  glen : (G hH s₀ k).length = k * H.D
  outB : bytesAt s.mem (out s₀) (done H s₀ k) = (G hH s₀ k).take (done H s₀ k)

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem loopRegs_ok (hH : HashOK H) {s : State} (h : KR (H := H) s₀ s) (h13 : s.gpr .r13 = s₀.gpr .rcx)
    (hS : States hH s₀ s.mem) :
    WP isa (.block H.loopRegs) s fun t => Inv hH s₀ 0 t ∧ t.zf = some (decide (ol s₀ = 0)) := by
  unfold Hash.loopRegs
  refine wp_mov fun s₁ u₁ _ _ => ?_
  refine wp_movm (a := A s₀ H.outO) (by rw [ea_nat, u₁.other _ (by decide), h.r15])
    (by rw [u₁.rd, u₁.wr]; exact InRegions.right' (in_sc hp hz h.wr (by
      have := layout (H := H); have := end_le hz; exact hz.o_outO_8_le_L))) fun s₂ u₂ => ?_
  refine wp_movm (a := s₀.gpr .rsp + BitVec.ofNat 64 8)
    (by rw [ea_nat, u₂.other _ (by decide), u₁.other _ (by decide), h.rsp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, hp.rd]
        exact ⟨argR s₀, by simp, contains_pre (by decide)⟩) fun s₃ u₃ => ?_
  refine wp_mov32i fun s₄ u₄ _ _ => wp_test fun s₅ g₅ m₅ rd₅ wr₅ z₅ => WP.block_nil ?_
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain r12 : s₅.gpr .r12 = BitVec.ofNat 64 (ol s₀) := by
    rw [g₅, u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, h.olW hp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain k₅ := (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  refine ⟨⟨k₅.same rd₅ wr₅ (by rw [g₅]) (by rw [g₅]) m₅, ?_, ?_, ?_, ?_, ?_,
    by simp [G], by simp [bytesAt]⟩, ?_⟩
  · rw [m₅, m₄]; exact hS
  · rw [g₅, u₄.gpr]; rfl
  · rw [g₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h13]
  · rw [r12]; simp
  · rw [g₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, h.outW]; simp
  · rw [z₅, BitVec.and_self, ← g₅, r12, ofNat_beq_zero (stackArg s₀ 0).isLt]

end

/-! ## Facts about words and lengths -/

theorem bytes32_int (i : Nat) : VG.Proof.MdStream.bytes32 true (BitVec.ofNat 32 i) = Spec.Pbkdf2.int i := by
  simp only [VG.Proof.MdStream.bytes32, ite_true, Spec.Pbkdf2.int, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  · exact Memory.mod32_div_mod8 i 24 (by decide)
  · exact Memory.mod32_div_mod8 i 16 (by decide)
  · exact Memory.mod32_div_mod8 i 8 (by decide)
  · rw [Nat.pow_zero, Nat.div_one]; exact Nat.mod_mod_of_dvd _ (by decide)

theorem sw32 (y : BitVec 32) : (y.setWidth 64).setWidth 32 = y := by
  have := y.isLt
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; omega_using []

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

/-! ## A step, before `T` is copied out -/

/-- The registers a step keeps until `T` is copied out. -/
abbrev mregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

theorem mregs_saved : ∀ r ∈ mregs, r ∈ calleeSaved := by decide

/-- In step `k`, before `T_{k+1}` is copied out: the key's states, the
registers, and the first `k` blocks in `out`. -/
structure Mid (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR (H := H) s₀ s
  st : States hH s₀ s.mem
  rbx : s.gpr .rbx = BitVec.ofNat 64 (k + 1)
  rbp : s.gpr .rbp = s₀.gpr .rcx
  r12 : s.gpr .r12 = BitVec.ofNat 64 (ol s₀ - k * H.D)
  r13 : s.gpr .r13 = out s₀ + BitVec.ofNat 64 (k * H.D)
  outB : bytesAt s.mem (out s₀) (k * H.D) = G hH s₀ k

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-- What a call (or a write) leaves, writing parts of `scratch` from the
working state on, or its working space, and the stack below `rsp`. -/
theorem Mid.call (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ mregs, s'.gpr r = s.gpr r)
    {ws : List Region} {n : Nat} (hn : n ≤ 24) (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ j, r = ⟨scr s₀, j⟩ ∧ j ≤ 8 * H.W) ∨
      ∃ o j, r = sR s₀ o j ∧ H.stWO ≤ o ∧ o + j ≤ (H.W + H.S) * 8) : Mid hH s₀ k s' := by
  obtain hst : H.sv + 64 = H.st0O := by simp [Hash.st0O]
  obtain ho : Region.Sub ⟨out s₀, k * H.D⟩ (outR s₀) := Region.sub_prefix hk
  obtain key : ∀ {X : Region}, (∀ o j, H.stWO ≤ o → o + j ≤ (H.W + H.S) * 8 → X.Disjoint (sR s₀ o j)) →
      X.Disjoint (lowR (H := H) s₀) → X.Disjoint (below (s.gpr .rsp) n) →
      ∀ r ∈ ws ++ [below (s.gpr .rsp) n], X.Disjoint r := by
    intro X h1 h2 h3 r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, ho1, ho2⟩
      · exact h2.sub_right (Region.sub_prefix hj)
      · exact h1 o j ho1 ho2
    · simp only [List.mem_singleton] at hr; subst hr; exact h3
  obtain hstk : ∀ {X : Region}, Region.Sub X (scR (H := H) s₀) → X.Disjoint (below (s.gpr .rsp) n) :=
    fun hX => (stk_sc hp h.kr hn hX).symm
  refine ⟨h.kr.keep hrd hwr (hcs _ (by simp)) (hcs _ (by simp)) hf
      (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega_using [h1, hz.o_sv_64_le_stWO])) (by exact hz.o_sv_64_le_L) h2) (low_disj hz (by exact hz.o_W8_le_sv) (by exact hz.o_sv_64_le_L))
        (hstk (part_sub (by exact hz.o_sv_64_le_L)))) (fun r hr => ?_),
    h.st.keep hz hH hf (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega_using [h1, hz.o_st0O_3mS_le_stWO])) (by exact hz.o_st0O_3mS_le_L) h2)
      (low_disj hz (by exact hz.o_W8_le_st0O) (by exact hz.o_st0O_3mS_le_L)) (hstk (part_sub (by exact hz.o_st0O_3mS_le_L)))),
    by rw [hcs _ (by simp), h.rbx], by rw [hcs _ (by simp), h.rbp],
    by rw [hcs _ (by simp), h.r12], by rw [hcs _ (by simp), h.r13], ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, _, h2⟩
      · exact ⟨scR (H := H) s₀, by simp, Region.sub_prefix (by show j ≤ (H.W + H.S) * 8; omega_using [hj])⟩
      · exact ⟨_, by simp, part_sub h2⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, stk_sub h.kr hn⟩
  · rw [← h.outB]
    exact bytes_keep hf (key (fun o j _ h2 => (hp.o_s.sub_left ho).sub_right (part_sub h2))
      ((hp.o_s.sub_left ho).sub_right low_sub) ((hp.stk_o.sub_left (stk_sub h.kr hn)).sub_right ho).symm)
      (by have := hp.onw; omega_using [hk, this])

/-- A write into a part of `scratch` from the working state on. -/
theorem Mid.write (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r ∈ mregs, s'.gpr r = s.gpr r) {o n : Nat}
    (ho : H.stWO ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [sR s₀ o n] s.mem s'.mem) :
    Mid hH s₀ k s' :=
  h.call hp hz hH hk hrd hwr hg (n := 0) (Nat.zero_le _) (hf.mono fun _ hr => List.mem_append_left _ hr)
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨o, n, rfl, ho, hon⟩

omit hp hz in
theorem Mid.upd {hH : HashOK H} {k : Nat} {s s' : State} (h : Mid hH s₀ k s) {d : Reg} {v : BitVec 64}
    (u : Upd s s' d v) (hd : d ∉ mregs) : Mid hH s₀ k s' := by
  obtain ne : ∀ r ∈ mregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u ⟨(ne _ (by simp)).symm, (ne _ (by simp)).symm⟩, u.mem ▸ h.st,
    by rw [u.other _ (ne _ (by simp)), h.rbx], by rw [u.other _ (ne _ (by simp)), h.rbp],
    by rw [u.other _ (ne _ (by simp)), h.r12], by rw [u.other _ (ne _ (by simp)), h.r13],
    by rw [u.mem, h.outB]⟩

end

/-! ## Copying `T` out -/

theorem ea_r13 (s : State) (k : Nat) (h14 : s.gpr .r14 = BitVec.ofNat 64 k) :
    s.ea { base := .r13, index := some .r14 } = s.gpr .r13 + BitVec.ofNat 64 k := by
  simp only [State.ea, h14]
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, BitVec.add_zero]

theorem outLoop_ok {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 31) {s : State} (hc : s.gpr .rcx = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 H.tO + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (s.gpr .r13 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr .r15 + BitVec.ofNat 64 H.tO, n⟩ ⟨s.gpr .r13, n⟩) :
    WP isa H.outLoop s fun t => VG.Proof.Pbkdf2.Md.X86_64.Calls.Copied s (s.gpr .r13)
      (bytesAt s.mem (s.gpr .r15 + BitVec.ofNat 64 H.tO) n) t := by
  generalize eA : s.gpr .r15 + BitVec.ofNat 64 H.tO = A at hin hsep ⊢
  generalize eB : s.gpr .r13 = B at hout hsep ⊢
  refine WP.seq (wp_mov32i fun s₀ u₀ _ _ => WP.block_nil ?_)
  obtain i0 : VG.Proof.Pbkdf2.Md.X86_64.Calls.CopyInv s A B 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r _ h => u₀.other r h, by rw [u₀.gpr]; rfl,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.count_loop hn _ (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  refine wp_movzx8 (a := A + BitVec.ofNat 64 k)
    (by rw [VG.Proof.Pbkdf2.Md.X86_64.Calls.ea_byteAt _ _ _ _ h.r14, h.other _ (by decide) (by decide), eA])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [ea_r13 _ k (by rw [u₁.other _ (by decide), h.r14]), u₁.other _ (by decide),
      h.other _ (by decide) (by decide), eB]) (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_cmp fun t₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  obtain h14 : t₃.gpr .r14 = BitVec.ofNat 64 (k + 1) := by
    rw [u₃.gpr, g₂, u₁.other _ (by decide), h.r14, VG.Proof.Pbkdf2.Md.X86_64.Calls.sx_one, ← ofNat_succ]
  obtain hcx : t₃.gpr .rcx = BitVec.ofNat 64 n := by
    rw [u₃.other _ (by decide), g₂, u₁.other _ (by decide), h.other _ (by decide) (by decide), hc]
  refine ⟨⟨by rw [rd₄, u₃.rd, rd₂, u₁.rd, h.rd], by rw [wr₄, u₃.wr, wr₂, u₁.wr, h.wr],
    fun r ha h14' => by rw [g₄, u₃.other r h14', g₂, u₁.other r ha, h.other r ha h14'],
    by rw [g₄, h14], ?_⟩, by rw [z₄, h14, hcx, sub_beq (by omega_using [hn', hk]) (by omega_using [hn'])]⟩
  obtain hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
  rw [m₄, u₃.mem, m₂, u₁.gpr, u₁.mem, h.mem, VG.Proof.Hmac.Generic.Common.bytesAt_snoc']
  obtain e : writeBytes s.mem B (bytesAt s.mem A k) (A + BitVec.ofNat 64 k) = s.mem (A + BitVec.ofNat 64 k) := by
    simp only [writeBytes, hl, VG.Proof.Hmac.Generic.Common.not_mem_of_disjoint hsep hk (Nat.le_of_lt hk)
      (by omega_using [hn']), ↓reduceIte]
  obtain e' := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem B (bytesAt s.mem A k)
    (s.mem (A + BitVec.ofNat 64 k)) (by rw [hl]; omega_using [hn', hk])
  rw [hl] at e'
  rw [e, show ((s.mem (A + BitVec.ofNat 64 k)).setWidth 64).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) by
    simp, e']

/-! ## A step: `U₁` -/

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-- `U₁ = PRF (S ‖ INT (k + 1))`. -/
abbrev U1 (hH : HashOK H) (s₀ : State) (k : Nat) : List Byte :=
  hmacBlockKey hH.SH.H (K0 hH s₀) (saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

/-- Before `update` with `INT (k + 1)`. -/
structure AtUpd (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s (A s₀ H.stWO) (A s₀ H.intO) (scr s₀) 4
  rsi : s.gpr .rsi = s₀.gpr .rcx + (BitVec.ofNat 32 H.P.B).signExtend 64
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀)
  int : bytesAt s.mem (A s₀ H.intO) 4 = Spec.Pbkdf2.int (k + 1)

/-- Before HMAC's `finalize`. -/
structure AtFin (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : FinArgs (H := H) s (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .rcx + (BitVec.ofNat 32 (H.P.B + 4)).signExtend 64)
    (A s₀ H.uO) (scr s₀)
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

/-- Before `iterate`. -/
structure AtIter (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : IterArgs (H := H) s (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO) (scr s₀)
  u : bytesAt s.mem (A s₀ H.uO) H.D = U1 hH s₀ k
  t : bytesAt s.mem (A s₀ H.tO) H.D = U1 hH s₀ k

/-- A copy of the salted inner state, `INT (k + 1)`, and `update`'s arguments. -/
theorem pieceA_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s : State} (h : Mid hH s₀ k s) :
    WP isa (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.stSO .r15 H.stWO H.S) (.block H.intArgs)) s
      (AtUpd hH s₀ k) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  obtain hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  obtain hk' := Nat.le_of_lt hkD
  obtain hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega_using [hk, this]
  obtain hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  -- The working state, copied.
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.copy_ok (src := .r15) (dst := .r15) (by decide)
    (by decide) (so := H.stSO) (d := H.stWO) (n := H.S) (by exact hz.o_0_lt_S) (by exact hz.o_S_lt_p31) (s := s)
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_stSO_S_le_L])))
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_stWO_S_le_L]))
    (by rw [h.kr.r15]; exact part_disj hz (Or.inl (by exact hz.o_stSO_S_le_stWO)) (by exact hz.o_stSO_S_le_L) (by exact hz.o_stWO_S_le_L))) fun s₁ c₁ => ?_)
  rw [h.kr.r15] at c₁
  obtain m₁ := h.write hp hz hH (Nat.le_of_lt hkD) c₁.rd c₁.wr (fun r hr => c₁.other r (by rintro rfl; simp at hr)
    (by rintro rfl; simp at hr)) (o := H.stWO) (n := H.S) (Nat.le_refl _) (by exact hz.o_stWO_S_le_L) (by
      rw [c₁.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _))
  obtain rs₁ : hH.SH.Repr s₁.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀) := by
    rw [c₁.mem]; exact repr_copy hH h.st.s
  -- `INT (k + 1)`.
  simp only [Hash.intArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov32r fun s₂ u₂ => wp_bswap32 fun s₃ u₃ => ?_
  obtain m₃ := (m₁.upd u₂ (by decide)).upd u₃ (by decide)
  refine wp_store32 (a := A s₀ H.intO) (by rw [ea_nat, m₃.kr.r15]) (in_sc hp hz m₃.kr.wr (by exact hz.o_intO_4_le_L))
    fun s₄ g₄ e₄ rd₄ wr₄ => ?_
  obtain f₄ : Frame [sR s₀ H.intO 4] s₃.mem s₄.mem := by
    rw [e₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain m₄ := m₃.write hp hz hH (Nat.le_of_lt hkD) rd₄ wr₄ (fun r _ => by rw [g₄]) (o := H.intO) (n := 4) (by exact hz.o_stWO_le_intO)
    (by exact hz.o_intO_4_le_L) f₄
  obtain e₄' : s₄.mem = writeBytes s₃.mem (A s₀ H.intO) (Spec.Pbkdf2.int (k + 1)) := by
    rw [e₄, u₃.gpr, u₂.gpr, m₁.rbx, sw32, sw32,
      show (BitVec.ofNat 64 (k + 1)).setWidth 32 = BitVec.ofNat 32 (k + 1) from
        BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using []),
      show bswap32 (BitVec.ofNat 32 (k + 1)) = if true then bswap32 (BitVec.ofNat 32 (k + 1)) else _ from rfl,
      writeW32, bytes32_int]
  -- `update`'s arguments.
  refine scr_ok m₄.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₅ u₅ => wp_mov fun s₆ u₆ _ _ => wp_addi fun s₇ u₇ => ?_
  obtain m₇ := ((m₄.upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)
  refine scr_ok m₇.kr.r15 (by exact hz.o_intO_lt_p31) fun s₈ u₈ => wp_mov32i fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ =>
    WP.block_nil ?_
  obtain m₁₀ := ((m₇.upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀ (by decide)
  obtain e₁₀ : s₁₀.mem = s₄.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  obtain ua : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s₁₀ (A s₀ H.stWO) (A s₀ H.intO) (scr s₀) 4 :=
    { rdi := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
          u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
      rdx := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
      rcx := by rw [u₁₀.other _ (by decide), u₉.gpr]; rfl
      r8 := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), m₇.kr.r15]
      cd := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := cov_part hp m₁₀.kr (o := H.intO) (n := 4) (by exact hz.o_intO_4_le_L)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp m₁₀.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_low hp m₁₀.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      d_st := part_disj hz (Or.inr (by exact hz.o_stWO_hsS_le_intO)) (by exact hz.o_intO_4_le_L) (by exact hz.o_stWO_hsS_le_L)
      d_sc := (low_disj hz (by exact hz.o_W8_le_intO) (by exact hz.o_intO_4_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      stk_st := stk_sc hp m₁₀.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_d := stk_sc hp m₁₀.kr (by decide) (part_sub (by exact hz.o_intO_4_le_L))
      stk_sc := stk_sc hp m₁₀.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }
  refine ⟨m₁₀, ua, ?_, by rw [e₁₀]; exact repr_keep hH f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by exact hz.o_stWO_S_le_intO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_intO_4_le_L)) (by rw [u₃.mem, u₂.mem]; exact rs₁),
    by rw [e₁₀, e₄', VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (by rfl) (by decide)]⟩
  rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr,
    u₅.other _ (by decide), m₄.rbp]

/-- `update` with `INT (k + 1)`. -/
theorem callA_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s : State} (h : AtUpd hH s₀ k s) :
    WP isa (.call H.updN H.updC) s fun t => Mid hH s₀ k t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  obtain hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  obtain hk' := Nat.le_of_lt hkD
  obtain hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega_using [hk, this]
  obtain hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_call hH.stream h.args (by decide) fun s₁₁ a₁₁ r₁₁ => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁₁.rd a₁₁.wr (fun r hr => a₁₁.cs r (mregs_saved r hr)) (by decide)
      a₁₁.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_stWO_hsS_le_L⟩
        · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  · have := r₁₁ _ h.repr (by
      rw [h.rsi, sx_ofNat (by exact hz.o_B_lt_p31), List.length_append, xorPad_length,
        blockKey_length, bytesAt_length, Nat.add_comm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    rwa [h.int] at this

/-- HMAC's `finalize`'s arguments. -/
theorem finArgs_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s : State} (h : Mid hH s₀ k s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.block H.finArgs) s (AtFin hH s₀ k) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega_using [hk, this]
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  -- `finalize`'s arguments.
  simp only [Hash.finArgs, List.append_assoc]
  refine scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₁ u₁ => ?_
  refine scr_ok ((u₁.other _ (by decide)).trans h.kr.r15) (by exact hz.o_st1O_lt_p31) fun s₂ u₂ => ?_
  simp only [List.cons_append]
  refine wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ => ?_
  have m₄ := (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  refine scr_ok m₄.kr.r15 (by exact hz.o_uO_lt_p31) fun s₅ u₅ => wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have m₆ := (m₄.upd u₅ (by decide)).upd u₆ (by decide)
  have e₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have stk : ∀ {o n : Nat}, o + n ≤ (H.W + H.S) * 8 → (below (s₆.gpr .rsp) 24).Disjoint (sR s₀ o n) :=
    fun h => stk_sc hp m₆.kr (Nat.le_refl _) (part_sub h)
  have fa : FinArgs (H := H) s₆ (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .rcx + (BitVec.ofNat 32 (H.P.B + 4)).signExtend 64)
      (A s₀ H.uO) (scr s₀) :=
    { rdi := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      rsi := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.gpr]
      rdx := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h.rbp]
      rcx := by rw [u₆.other _ (by decide), u₅.gpr]
      r8 := by rw [u₆.gpr, u₅.other _ (by decide), m₄.kr.r15]
      cr := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := cov_part hp m₆.kr (o := H.st1O) (n := H.S) (by exact hz.o_st1O_S_le_L)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp m₆.kr (by exact hz.o_stWO_S_le_L)
        · exact cov_part hp m₆.kr (by exact hz.o_uO_D_le_L)
        · exact cov_low hp m₆.kr (by exact hz.o_W8_le_L)
      i_u := part_disj hz (Or.inr (by exact hz.o_st1O_S_le_stWO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_st1O_S_le_L)
      i_o := part_disj hz (Or.inl (by exact hz.o_stWO_S_le_uO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_uO_D_le_L)
      i_s := low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_S_le_L)
      u_o := part_disj hz (Or.inl (by exact hz.o_st1O_S_le_uO)) (by exact hz.o_st1O_S_le_L) (by exact hz.o_uO_D_le_L)
      u_s := low_disj hz (by exact hz.o_W8_le_st1O) (by exact hz.o_st1O_S_le_L)
      o_s := low_disj hz (by exact hz.o_W8_le_uO) (by exact hz.o_uO_D_le_L)
      stk_i := stk (by exact hz.o_stWO_S_le_L)
      stk_u := stk (by exact hz.o_st1O_S_le_L)
      stk_o := stk (by exact hz.o_uO_D_le_L)
      stk_s := stk_sc hp m₆.kr (Nat.le_refl _) low_sub
      scnw := by have := hp.snw; omega_using [this] }
  exact ⟨m₆, fa, by rw [e₆]; exact hr⟩

/-- HMAC's `finalize`: `U₁`. -/
theorem callB_ok (hH : HashOK H) (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2) {k : Nat} (hk : k < nb H s₀) {s : State}
    (h : AtFin hH s₀ k s) :
    WP isa (.call H.hmacFinN H.hmacFin) s fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.uO) H.D = U1 hH s₀ k := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  obtain hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  obtain hk' := Nat.le_of_lt hkD
  obtain hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega_using [hk, this]
  obtain hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  refine hfin_call hH hF hFsp hFd h.args fun s₇ rd₇ wr₇ cs₇ f₇ hpost => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' rd₇ wr₇ (fun r hr => cs₇ r (mregs_saved r hr)) (Nat.le_refl _) f₇
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_stWO_S_le_L⟩
        · exact .inr ⟨_, _, rfl, by exact hz.o_stWO_le_uO, by exact hz.o_uO_D_le_L⟩
        · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · have hK := blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
    exact hpost _ _ hK (by rw [hK, List.length_append, bytesAt_length]; simp [Spec.Pbkdf2.int]; have := hz.o_B_5_le_L; omega_using [hsl, this])
      (by rw [← List.append_assoc]; exact h.repr)
      (by
        rw [sx_ofNat (by exact hz.o_B_4_lt_p31), List.length_append, bytesAt_length,
          show (Spec.Pbkdf2.int (k + 1)).length = 4 from rfl]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have : sl s₀ = (s₀.gpr .rcx).toNat := rfl
        omega_using [this])
      h.mid.st.o

/-- `U` copied to `T`, and `iterate`'s arguments. -/
theorem pieceC_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s₇ : State} (m₇ : Mid hH s₀ k s₇)
    (hU : bytesAt s₇.mem (A s₀ H.uO) H.D = U1 hH s₀ k) :
    WP isa (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.uO .r15 H.tO H.D) (.block H.iterArgs)) s₇
      (AtIter hH s₀ k) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  obtain hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  obtain hk' := Nat.le_of_lt hkD
  obtain hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega_using [hk, this]
  obtain hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  -- `U` copied to `T`.
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.copy_ok (src := .r15) (dst := .r15) (by decide)
    (by decide) (so := H.uO) (d := H.tO) (n := H.D) hD.1 (by exact hz.o_D_lt_p31) (s := s₇)
    (fun j hj => by rw [m₇.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz m₇.kr.wr (by omega_using [hj, hz.o_uO_D_le_L])))
    (fun j hj => by rw [m₇.kr.r15, add_ofNat]; exact in_sc hp hz m₇.kr.wr (by omega_using [hj, hz.o_tO_D_le_L]))
    (by rw [m₇.kr.r15]; exact part_disj hz (Or.inl (by exact hz.o_uO_D_le_tO)) (by exact hz.o_uO_D_le_L) (by exact hz.o_tO_D_le_L))) fun s₈ c₈ => ?_)
  rw [m₇.kr.r15] at c₈
  obtain f₈ : Frame [sR s₀ H.tO H.D] s₇.mem s₈.mem := by
    rw [c₈.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain m₈ := m₇.write hp hz hH hk' c₈.rd c₈.wr (fun r hr => c₈.other r (by rintro rfl; simp at hr)
    (by rintro rfl; simp at hr)) (o := H.tO) (n := H.D) (by exact hz.o_stWO_le_tO) (by exact hz.o_tO_D_le_L) f₈
  obtain hU₈ : bytesAt s₈.mem (A s₀ H.uO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D :=
    bytes_keep f₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by exact hz.o_uO_D_le_tO)) (by exact hz.o_uO_D_le_L) (by exact hz.o_tO_D_le_L)) (by exact hz.o_D_le_p64)
  obtain hT₈ : bytesAt s₈.mem (A s₀ H.tO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D := by
    rw [c₈.mem]; exact VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by exact hz.o_D_lt_p64)
  -- `iterate`'s arguments.
  simp only [Hash.iterArgs, List.append_assoc]
  refine scr_ok m₈.kr.r15 (by exact hz.o_st0O_lt_p31) fun s₉ u₉ => ?_
  refine scr_ok ((u₉.other _ (by decide)).trans m₈.kr.r15) (by exact hz.o_uO_lt_p31) fun s₁₀ u₁₀ => ?_
  obtain m₁₀ := (m₈.upd u₉ (by decide)).upd u₁₀ (by decide)
  simp only [List.cons_append, List.nil_append]
  refine wp_movm (a := A s₀ H.cO) (by rw [ea_nat, m₁₀.kr.r15])
    (InRegions.right' (in_sc hp hz m₁₀.kr.wr (by exact hz.o_cO_8_le_L))) fun s₁₁ u₁₁ => ?_
  obtain m₁₁ := m₁₀.upd u₁₁ (by decide)
  refine scr_ok m₁₁.kr.r15 (by exact hz.o_tO_lt_p31) fun s₁₂ u₁₂ => wp_mov fun s₁₃ u₁₃ _ _ => WP.block_nil ?_
  obtain m₁₃ := (m₁₁.upd u₁₂ (by decide)).upd u₁₃ (by decide)
  obtain e₁₃ : s₁₃.mem = s₈.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  obtain stk' : ∀ {o n : Nat}, o + n ≤ (H.W + H.S) * 8 → (below (s₁₃.gpr .rsp) 24).Disjoint (sR s₀ o n) :=
    fun h => stk_sc hp m₁₃.kr (Nat.le_refl _) (part_sub h)
  obtain ia : IterArgs (H := H) s₁₃ (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO) (scr s₀) :=
    { rdi := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
          u₁₀.other _ (by decide), u₉.gpr]
      rsi := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr]
      rdx := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, m₁₀.kr.cW]
      rcx := by rw [u₁₃.other _ (by decide), u₁₂.gpr]
      r8 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), m₁₁.kr.r15]
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
      stk_k := stk' (by exact hz.o_st0O_2mS_le_L)
      stk_u := stk' (by exact hz.o_uO_D_le_L)
      stk_t := stk' (by exact hz.o_tO_D_le_L)
      stk_s := stk_sc hp m₁₃.kr (Nat.le_refl _) low_sub
      knw := by
        have := hp.snw
        simp only [A, BitVec.toNat_add, BitVec.toNat_ofNat]
        have := hz.o_st0O_2mS_le_L; have := L_lt hz; omega_arith
      scnw := by have := hp.snw; omega_using [this] }
  exact ⟨m₁₃, ia, by rw [e₁₃, hU₈, hU], by rw [e₁₃, hT₈, hU]⟩

/-- `iterate`: `T_{k+1}`. -/
theorem callC_ok (hH : HashOK H) (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate)
    (hId : H.iterate.depth ≤ 2) {k : Nat} (hk : k < nb H s₀) {s : State} (h : AtIter hH s₀ k s) :
    WP isa (.call H.iterN H.iterate) s fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.tO) H.D = Tb hH s₀ (k + 1) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  obtain hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  obtain hk' := Nat.le_of_lt hkD
  obtain hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega_using [hk, this]
  obtain hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  refine iter_call hH hI hIsp hId h.args fun s₁₄ rd₁₄ wr₁₄ cs₁₄ f₁₄ hpost' => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' rd₁₄ wr₁₄ (fun r hr => cs₁₄ r (mregs_saved r hr)) (Nat.le_refl _) f₁₄
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr ⟨_, _, rfl, by exact hz.o_stWO_le_tO, by exact hz.o_tO_D_le_L⟩
        · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  obtain hK := blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  obtain hc : ((BitVec.ofNat 64 (cc s₀ - 1)).setWidth 32).toNat = cc s₀ - 1 := by
    have := ((s₀.gpr .r8).setWidth 32).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using []
  obtain hO : A s₀ H.st0O + BitVec.ofNat 64 H.S = A s₀ H.st1O := by
    rw [add_ofNat, show H.st0O + H.S = H.st1O by exact hz.o_st0O_S_eq_st1O]
  obtain ho : hH.SH.Repr s.mem (A s₀ H.st0O + BitVec.ofNat 64 H.S) (xorPad (K0 hH s₀) opad) := by
    rw [hO]; exact h.mid.st.o
  rw [hpost' _ hK h.mid.st.i ho, hc, h.u, h.t]
  rfl

/-! ## A step: copying `T` out -/

omit hp hz in
theorem Mid.same {hH : HashOK H} {k : Nat} {s s' : State} (h : Mid hH s₀ k s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) : Mid hH s₀ k s' :=
  ⟨h.kr.same hrd hwr (by rw [hg]) (by rw [hg]) hm, hm ▸ h.st, by rw [hg, h.rbx], by rw [hg, h.rbp],
    by rw [hg, h.r12], by rw [hg, h.r13], by rw [hm, h.outB]⟩

omit hp in
/-- The bytes of `T` the output still needs. -/
theorem outLen_ok {hH : HashOK H} {k : Nat} {s : State} (h : Mid hH s₀ k s) :
    WP isa H.outLen s fun t => Mid hH s₀ k t ∧ t.gpr .rcx = BitVec.ofNat 64 (min (ol s₀ - k * H.D) H.D) ∧
      t.mem = s.mem := by
  obtain hD := hz.z.D; have hN := hz.z.N
  obtain hol : ol s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
  unfold Hash.outLen
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => wp_cmp fun s₂ g₂ m₂ rd₂ wr₂ c₂ _ => WP.block_nil ?_)
  obtain e₂ : s₂.mem = s.mem := by rw [m₂, u₁.mem]
  obtain m₂ := (h.upd u₁ (by decide)).same rd₂ wr₂ g₂ m₂
  obtain rcx : s₂.gpr .rcx = BitVec.ofNat 64 H.D := by rw [g₂, u₁.gpr, zx_ofNat (by exact hz.o_D_lt_p32)]
  obtain cf : s₂.cf = some (decide (ol s₀ - k * H.D < H.D)) := by
    rw [c₂, ← g₂, m₂.r12, rcx, toNat_ofNat_lt (by omega_using [hol]), toNat_ofNat_lt (by exact hz.o_D_lt_p64)]
  refine WP.ite (decide (ol s₀ - k * H.D < H.D)) (by simp [eval, cf]) (fun hT => ?_) fun hF => WP.block_nil ?_
  · refine wp_mov fun s₃ u₃ _ _ => WP.block_nil ⟨m₂.upd u₃ (by decide), ?_, by rw [u₃.mem, e₂]⟩
    have : ol s₀ - k * H.D < H.D := of_decide_eq_true hT
    rw [u₃.gpr, m₂.r12, Nat.min_eq_left (Nat.le_of_lt this)]
  · have : ¬ ol s₀ - k * H.D < H.D := of_decide_eq_false (by simpa using hF)
    exact ⟨m₂, by rw [rcx, Nat.min_eq_right (by omega_using [this])], e₂⟩

/-- Copying as much of `T_{k+1}` as the output needs, and on to the next block. -/
theorem tail_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) (hg : (G hH s₀ k).length = k * H.D) {s : State}
    (h : Mid hH s₀ k s) (ht : bytesAt s.mem (A s₀ H.tO) H.D = Tb hH s₀ (k + 1)) :
    WP isa (.seq H.outLen (.seq H.outLoop (.block Hash.advance))) s fun t =>
      Inv hH s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = nb H s₀)) := by
  obtain hL := L_lt hz
  obtain hD := hz.z.D; have hN := hz.z.N
  obtain hol : ol s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
  obtain hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  obtain hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega_using [hk, this]
  obtain hk1 := lt_nb (s₀ := s₀) hD.1 (k := k + 1)
  rw [Nat.succ_mul] at hk1
  have hon := hp.onw
  generalize en : min (ol s₀ - k * H.D) H.D = n
  obtain hn : 0 < n ∧ n ≤ H.D ∧ k * H.D + n ≤ ol s₀ := by omega_using [hD, hkD, en]
  obtain hdn : done H s₀ (k + 1) = k * H.D + n := by
    show min ((k + 1) * H.D) (ol s₀) = _; rw [Nat.succ_mul]; omega_using [en, hn]
  obtain osub : Region.Sub ⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ (outR s₀) := Offset.sub_base _ hn.2.2
  refine WP.seq (WP.mono (outLen_ok hz h) fun s₁ ⟨m₁, rc₁, e₁⟩ => ?_)
  rw [en] at rc₁
  refine WP.seq (WP.mono (outLoop_ok (n := n) hn.1 (by omega_using [hD, hN, hn]) rc₁
    (fun j hj => by rw [m₁.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz m₁.kr.wr (by omega_using [hj, hn.2.1, hz.o_tO_D_le_L])))
    (fun j hj => by
      rw [m₁.r13, add_ofNat]
      exact ⟨outR s₀, by rw [m₁.kr.wr, hp.wr]; simp, Offset.contains_base _ (by omega_using [hn, hj]) (by omega_using [hon, hn, hj])⟩)
    (by rw [m₁.kr.r15, m₁.r13]; exact ((hp.o_s.sub_left osub).sub_right (part_sub (by omega_using [hn.2.1, hz.o_tO_D_le_L]))).symm))
    fun s₂ c₂ => ?_)
  rw [m₁.kr.r15, m₁.r13] at c₂
  obtain f₂ : Frame [(⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)] s₁.mem s₂.mem := by
    rw [c₂.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain od : ∀ {X : Region}, Region.Sub X (scR (H := H) s₀) →
      ∀ r ∈ [(⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)], X.Disjoint r := fun hX r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hp.o_s.sub_left osub).sub_right hX).symm
  obtain k₂ : KR (H := H) s₀ s₂ := m₁.kr.keep c₂.rd c₂.wr (c₂.other _ (by decide) (by decide))
    (c₂.other _ (by decide) (by decide)) f₂ (od (part_sub (by exact hz.o_sv_64_le_L))) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩
  refine wp_add fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_
  obtain g₄ : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .r13 → r ≠ .rbx → s₄.gpr r = s₁.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h4, u₃.other r h3, c₂.other r h1 h2]
  obtain e₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨((k₂.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [e₅]; exact m₁.st.keep hz hH f₂ (od (part_sub (by exact hz.o_st0O_3mS_le_L)))
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), c₂.other _ (by decide) (by decide), m₁.rbx,
      VG.Proof.Pbkdf2.Md.X86_64.Calls.sx_one, ← ofNat_succ]
  · rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), m₁.rbp]
  · rw [u₅.gpr, g₄ _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide) (by decide)
      (by decide), m₁.r12, rc₁, sub_ofNat (by omega_using [hn]), hdn]
    congr 1; omega_using []
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, c₂.other _ (by decide) (by decide),
      c₂.other _ (by decide) (by decide), m₁.r13, rc₁, add_ofNat, hdn]
  · rw [G_succ, List.length_append, hg, ← ht, bytesAt_length, Nat.succ_mul]
  · rw [e₅, hdn, bytesAt_add, bytes_keep f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hon, hn])).symm)
      (by omega_using [hon, hn]),
      c₂.mem, VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hol, hn]),
      m₁.outB, G_succ, ← hg, List.take_length_add_append, ← ht, e₁, ← bytesAt_take _ _ hn.2.1]
  · rw [z₅, g₄ _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide) (by decide)
      (by decide), m₁.r12, rc₁, sub_beq (by omega_using [hol]) (by omega_using [hol, hn])]
    simp only [Option.some.injEq, decide_eq_decide]
    omega_using [hk, hk1, en]

/-! ## The loop and `pbkdf2` -/

/-- One block of the output. -/
theorem block_ok (hH : HashOK H) (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
    (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2)
    {k : Nat} (hk : k < nb H s₀) {s : State} (h : Inv hH s₀ k s) :
    WP isa H.block s fun t => Inv hH s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = nb H s₀)) := by
  obtain hkD : k * H.D < ol s₀ := (lt_nb hz.z.D.1).1 hk
  obtain hd : done H s₀ k = k * H.D := by show min _ _ = _; omega_using [hkD]
  have hb := h.outB
  rw [hd, List.take_of_length_le (Nat.le_of_eq h.glen)] at hb
  obtain m : Mid hH s₀ k s := ⟨h.kr, h.st, h.rbx, h.rbp, by rw [h.r12, hd], by rw [h.r13, hd], hb⟩
  unfold Hash.block
  refine WP.assoc (WP.seq (WP.mono (pieceA_ok hp hz hH hk m) fun s₁ h₁ => ?_))
  refine WP.seq (WP.mono (callA_ok hp hz hH hk h₁) fun s₂ ⟨m₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (finArgs_ok hp hz hH hk m₂ r₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (callB_ok hp hz hH hF hFsp hFd hk h₃) fun s₄ ⟨m₄, u₄⟩ => ?_)
  refine WP.assoc (WP.seq (WP.mono (pieceC_ok hp hz hH hk m₄ u₄) fun s₅ h₅ => ?_))
  refine WP.seq (WP.mono (callC_ok hp hz hH hI hIsp hId hk h₅) fun s₆ ⟨m₆, t₆⟩ => ?_)
  exact tail_ok hp hz hH hk h.glen m₆ t₆

/-- The loop over the blocks of the output: none when `out_len = 0`. -/
theorem loop_ok (hH : HashOK H) (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
    (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2)
    {s : State} (h : Inv hH s₀ 0 s) (hz0 : s.zf = some (decide (ol s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop H.block .ne)) s (Inv hH s₀ (nb H s₀)) := by
  have hD := hz.z.D.1
  refine WP.ite (decide (ol s₀ = 0)) (by simp [eval, hz0]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · rw [(nb_zero hD).2 (of_decide_eq_true h0)]; exact h
  · have : nb H s₀ ≠ 0 := fun e => by simp [(nb_zero hD).1 e] at h0
    exact VG.Proof.Pbkdf2.Md.X86_64.Calls.count_loop (Nat.pos_of_ne_zero this) (Inv hH s₀)
      (fun k hk t ht => block_ok hp hz hH hF hFsp hFd hI hIsp hId hk ht) h

theorem correct (hH : HashOK H) (hIn : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hInsp : NoSp H.hmacInit) (hInd : H.hmacInit.depth ≤ 2)
    (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
    (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2) :
    WP isa H.pbkdf2 s₀ fun s' => gprPreserved s₀ s' ∧ (pbkG hH.SH (H.W + H.S)).post s₀ s' := by
  obtain hD := hz.z.D.1; have hW := hz.W
  unfold Hash.pbkdf2
  refine WP.seq (WP.mono (loadScr_ok hp) fun s₀' l => ?_)
  refine WP.seq (WP.mono (entry_ok hp hz l) fun s₁ ⟨k₁, bx, bp, r12, r13, cf⟩ => ?_)
  refine WP.seq (WP.mono (key_ok hp hz hH ⟨k₁, bx, bp, r12, r13⟩ cf) fun s₂ ⟨k₂, dx₂, cx₂, ka⟩ => ?_)
  refine WP.seq (WP.mono (setup_ok hp hz hH hIn hInsp hInd k₂ dx₂ cx₂ ka) fun s₃ ⟨k₃, st₃⟩ => ?_)
  refine WP.seq (WP.mono (loopRegs_ok hp hz hH k₃.kr k₃.r13 st₃) fun s₄ ⟨i₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hp hz hH hF hFsp hFd hI hIsp hId i₄ z₄) fun s₅ i₅ => ?_)
  have k₅ := i₅.kr
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.restore_ok H.hh k₅.r15 hW k₅.saved (in_wr hp k₅)
    (by have : H.S = H.P.N + H.P.B := rfl; have := hz.z.B; show 8 * H.W + 48 ≤ (H.W + H.S) * 8; exact hz.o_W8_48_le_L))
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm, k₅.ret hp]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₅.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  obtain hdone : done H s₀ (nb H s₀) = ol s₀ := by
    have := ol_le (s₀ := s₀) hD; show min _ _ = _; omega_using [this]
  have hb := i₅.outB
  rw [hdone] at hb
  show Spec.Pbkdf2.pbkdf2 (Spec.Hmac.hmac hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))) hH.SH.digestBytes
    (saltB s₀) (cc s₀) (ol s₀) = some (bytesAt s'.mem (out s₀) (ol s₀))
  have hol := hp.olD
  rw [hH.hD, Spec.Pbkdf2.pbkdf2, ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [hol])), hm, hb]
  rfl

end

end VG.Proof.Pbkdf2.Md.X86_64.Pbk
