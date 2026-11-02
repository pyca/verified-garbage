module

public import VerifiedGarbage.Spec.RsaOaep.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Base
public import VerifiedGarbage.Impl.RsaOaep.RISCV64.Decrypt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# RSAES-OAEP decryption on RISC-V: the precondition and the entry

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Pre.lean`, `Dc/Entry.lean`): `PreD s`, the shared
contract's precondition (`Spec.RsaOaep.decryptContract`, with the stack of
the frames and of `vg_rsa_private_checked`, `stackBytes`), by name
(`preD_of`); the working space `Sd s` and the values the decoding keeps in
`s1`–`s4` (`vD s rc`, with the private operation's result `rc` in `s4`),
both functions of the entry state `s` alone, as `Base` takes them; `fits`,
`Fits` for any state with `s`'s stack pointer and regions; and `entry_ok`:
the saves and the prologue leave our caller's registers and return address
in their slots and `s0`–`s3` holding `scratch`, `k`, `out` and `msg_len`
(`Entered`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes oRsa save)
open VG.Impl.RsaOaep.RISCV64.Dec (privBytes prologue)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off fx kR fb fr save_ok Saves fb_al stackArgAddr_eq)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_ld wp_mov wp_addSp wp_nil)

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

/-- The stack the function uses: its frame (`frameBytes`), the private
operation's (`privBytes`) and that function's own. -/
def stackBytes : Nat := frameBytes + privBytes + Impl.Rsa.RISCV64.Priv.frameBytes

theorem stackBytes_eq : stackBytes = 3472 := rfl

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev mlR (s : State) : Region := ⟨s.gpr .a2, 8⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
abbrev pR (s : State) : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 7, (stackArg s 8).toNat⟩
abbrev lR (s : State) : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
abbrev ctR (s : State) : Region := ⟨stackArg s 11, (stackArg s 12).toNat⟩
abbrev scR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 120⟩
/-- The stack the function uses. -/
abbrev kD (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩

/-- What the code needs of `decryptContract.pre`, by name. -/
structure PreD (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  sp1 : stackBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 120 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, pR s, qR s, dpR s, dqR s, qiR s, lR s, ctR s, aR s]
  hwr : s.wr = [oR s, mlR s, scR s]
  oml : (oR s).Disjoint (mlR s)
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  ol : (oR s).Disjoint (lR s)
  oct : (oR s).Disjoint (ctR s)
  os : (oR s).Disjoint (scR s)
  oa : (oR s).Disjoint (aR s)
  mln : (mlR s).Disjoint (nR s)
  mle : (mlR s).Disjoint (eR s)
  mlp : (mlR s).Disjoint (pR s)
  mlq : (mlR s).Disjoint (qR s)
  mldp : (mlR s).Disjoint (dpR s)
  mldq : (mlR s).Disjoint (dqR s)
  mlqi : (mlR s).Disjoint (qiR s)
  mll : (mlR s).Disjoint (lR s)
  mlct : (mlR s).Disjoint (ctR s)
  mls : (mlR s).Disjoint (scR s)
  mla : (mlR s).Disjoint (aR s)
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ps : (pR s).Disjoint (scR s)
  qs : (qR s).Disjoint (scR s)
  dps : (dpR s).Disjoint (scR s)
  dqs : (dqR s).Disjoint (scR s)
  qis : (qiR s).Disjoint (scR s)
  ls : (lR s).Disjoint (scR s)
  cts : (ctR s).Disjoint (scR s)
  sa : (scR s).Disjoint (aR s)
  ko : (kD s).Disjoint (oR s)
  kml : (kD s).Disjoint (mlR s)
  kn : (kD s).Disjoint (nR s)
  ke : (kD s).Disjoint (eR s)
  kp : (kD s).Disjoint (pR s)
  kq : (kD s).Disjoint (qR s)
  kdp : (kD s).Disjoint (dpR s)
  kdq : (kD s).Disjoint (dqR s)
  kqi : (kD s).Disjoint (qiR s)
  kl : (kD s).Disjoint (lR s)
  kct : (kD s).Disjoint (ctR s)
  ks : (kD s).Disjoint (scR s)
  ka : (kD s).Disjoint (aR s)
  wo : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wml : (s.gpr .a2).toNat + 8 ≤ 2 ^ 64
  wn : (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64
  we : (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64
  wp : (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wq : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wdp : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wdq : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wqi : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wl : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  wct : (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64
  wsc : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a4).toNat
  k2 : (s.gpr .a4).toNat ≤ 1024
  ok : (s.gpr .a1).toNat = (s.gpr .a4).toNat
  oc : (stackArg s 12).toNat = (s.gpr .a4).toNat
  e1 : 1 ≤ (s.gpr .a6).toNat
  e2 : (s.gpr .a6).toNat ≤ (s.gpr .a4).toNat
  p1 : 1 ≤ (stackArg s 0).toNat
  p2 : (stackArg s 0).toNat < (s.gpr .a4).toNat
  q1 : 1 ≤ (stackArg s 2).toNat
  q2 : (stackArg s 2).toNat < (s.gpr .a4).toNat
  h4 : (stackArg s 4).toNat = (stackArg s 0).toNat
  h8 : (stackArg s 8).toNat = (stackArg s 0).toNat
  h6 : (stackArg s 6).toNat = (stackArg s 2).toNat
  hs : Spec.RsaPss.scratchWords (s.gpr .a4).toNat ≤ (stackArg s 14).toNat
  alm : (s.gpr .a2).toNat % 8 = 0
  als : (stackArg s 13).toNat % 8 = 0

theorem preD_of {H G : Spec.Mgf1.Hash} {s : State}
    (h : (Spec.RsaOaep.decryptContract H G abi stackBytes).pre s) : PreD s := by
  have e : stackBytes = 3471 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs,
    stackArgs_fifteen, List.append_eq, Spec.Rsa.lenValid] at h
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil] at h
  obtain ⟨spal, sp1, sp2, hrd, hwr, oml, on, ⟨oe, op, oq, odp, odq, oqi, ol, oct, os, oa, mln, mle, mlp, mlq, mldp,
    mldq, mlqi, mll, mlct, mls, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts, sa⟩, ko, kml, kn, ke, kp, kq, kdp, kdq,
    kqi, kl, kct, ks, ka, wo, wml, wn, we, wp, wq, wdp, wdq, wqi, wl, wct, wsc, k1, k2, ok, oc, e1, e2, p1, p2, q1,
    q2, h4, h8, h6, hs, alm, als⟩ := h
  exact ⟨spal, sp1, sp2, hrd, hwr, oml, on, oe, op, oq, odp, odq, oqi, ol, oct, os, oa, mln, mle, mlp, mlq, mldp,
    mldq, mlqi, mll, mlct, mls, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts, sa, ko, kml, kn, ke, kp, kq, kdp, kdq,
    kqi, kl, kct, ks, ka, wo, wml, wn, we, wp, wq, wdp, wdq, wqi, wl, wct, wsc, k1, k2, ok, oc, e1, e2, p1, p2, q1,
    q2, h4, h8, h6, hs, alm, als⟩

/-! ## The working space and the registers the decoding keeps -/

/-- The working space. -/
abbrev Sd (s : State) : Addr := stackArg s 13

/-- `k`. -/
abbrev kk (s : State) : Nat := (s.gpr .a4).toNat

/-- The values `Base` fixes in `s1`–`s4` once the private operation has
returned `rc`: `k`, `out`, `msg_len` and `rc`. -/
def vD (s : State) (rc : Nat) : Reg → BitVec 64
  | .s1 => s.gpr .a4
  | .s2 => s.gpr .a0
  | .s3 => s.gpr .a2
  | .s4 => BitVec.ofNat 64 rc
  | _ => 0

/-- The working space and `vD`, as `Base` takes them: of the entry state `s`,
whatever the state. -/
abbrev SD (s : State) : State → Addr := fun _ => Sd s
abbrev VD (s : State) (rc : Nat) : State → Reg → BitVec 64 := fun _ => vD s rc

section
variable {s : State} (P : PreD s)
include P

theorem scLen : oRsa ≤ (stackArg s 14).toNat * 8 := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; unfold oRsa; omega

theorem sc_sub : Region.Sub (SC (SD s) s) (scR s) := Region.sub_prefix (scLen P)

omit P in
theorem kR_sub : Region.Sub (kR s) (kD s) := below_sub (by rw [stackBytes_eq]; decide) (by rw [stackBytes_eq]; decide)

/-- `Fits` for any state with the entry's stack pointer and regions. -/
theorem fits {s' : State} (hsp : s'.sp = s.sp) (hwr : s'.wr = s.wr) : Fits (SD s) s' where
  sp1 := by rw [hsp]; have := P.sp1; rw [stackBytes_eq] at this; unfold Proof.RsaOaep.RISCV64.stackBytes; omega
  sp16 := by rw [hsp]; exact P.spal
  sc := ⟨scR s, by rw [hwr, P.hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
    rfl, scLen P⟩
  ksc := by
    have e : kR s' = kR s := by simp only [kR, hsp]
    rw [e]; exact (P.ks.sub_left kR_sub).sub_right (sc_sub P)
  wS := by show (stackArg s 13).toNat + oRsa ≤ 2 ^ 64; have := P.wsc; have := scLen P; omega

end

section
variable {s s' t : State} {rc : Nat} (h : Base (SD s) (VD s rc) s' t)
include h

theorem Base.dk : t.gpr .s1 = s.gpr .a4 := h.vs .s1 (by decide)
theorem Base.dout : t.gpr .s2 = s.gpr .a0 := h.vs .s2 (by decide)
theorem Base.dml : t.gpr .s3 = s.gpr .a2 := h.vs .s3 (by decide)
theorem Base.drc : t.gpr .s4 = BitVec.ofNat 64 rc := h.vs .s4 (by decide)

end

/-! ## The entry -/

/-- The stack arguments are in `aR`. -/
theorem in_aR {s : State} {j : Nat} (hj : j < 15) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-- After the saves and the prologue: our caller's registers and return
address in their slots, `s0`–`s3` holding `scratch`, `k`, `out` and
`msg_len`, and `a3`, `a5`–`a7` the entry's `n`, `e`, `e_len` and `p`. -/
structure Entered (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  s0 : t.gpr .s0 = Sd s
  s1 : t.gpr .s1 = s.gpr .a4
  s2 : t.gpr .s2 = s.gpr .a0
  s3 : t.gpr .s3 = s.gpr .a2
  args : ∀ r ∈ [Reg.a3, .a5, .a6, .a7], t.gpr r = s.gpr r
  mem : Frame [kR s] s.mem t.mem

section
variable {s : State} (P : PreD s)
include P

theorem arg_al {j : Nat} (hj : j < 15) : (stackArgAddr s j).toNat % 8 = 0 := by
  have := P.spal; have := P.sp2
  have e : (stackArgAddr s j).toNat = s.sp.toNat + 8 * j := by
    simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e]; omega

theorem fb_al8 : (fb s).toNat % 8 = 0 := by
  have := fb_al (fits P (s' := s) rfl rfl); omega

/-- A load of our stack argument `j` through `t6`, the entry stack pointer,
with memory changed only in the stack and our part of the working space. -/
theorem wp_arg {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 15)
    (h6 : t.gpr .t6 = s.sp) (hrd : t.rd = s.rd) (hm : Frame [kR s, SC (SD s) s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .t6 (8 * j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h6]; rfl) (arg_al P hj) ?_ (fun t' o e => k t' o ?_) ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (P.ka.sub_left kR_sub).symm
      · exact (P.sa.sub_left (sc_sub P)).symm) (by decide)]

theorem entry_ok : WP isa (.block (save ++ prologue)) (allocd frameBytes s) (Entered s) := by
  refine save_ok (u := allocd frameBytes s) rfl rfl (fb_al8 P) (Frame.refl _ _) (fun r _ => rfl)
    fun v kv h0 hm hsv => ?_
  have hrd : v.rd = s.rd := kv.rd
  have hsp : v.sp = fb s := kv.sp
  have hm2 : Frame [kR s, SC (SD s) s] s.mem v.mem := hm.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  have gs : ∀ r ∈ [Reg.a0, .a2, .a3, .a4, .a5, .a6, .a7], v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r (by revert r; decide)]; rfl
  simp only [prologue, Impl.RsaOaep.RISCV64.argBase]
  refine wp_addSp fun v₁ o₁ e₁ => ?_
  have g6 : v₁.gpr .t6 = s.sp := by rw [e₁, hsp, BitVec.sub_add_cancel]
  refine wp_arg P (j := 13) (by decide) g6 (o₁.rd.trans hrd) (by rw [o₁.mem]; exact hm2) fun v₂ o₂ e₂ => ?_
  refine wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ => wp_mov fun w ow ew => wp_nil ?_
  have kw : Only [.t6, .s0, .s1, .s2, .s3] v w := (o₁.trans (o₂.trans (o₃.trans (o₄.trans ow)))).mono
  have a2 : ∀ r ∈ [Reg.a0, .a2, .a3, .a4, .a5, .a6, .a7], v₂.gpr r = s.gpr r := fun r hr => by
    rw [(o₁.trans o₂).get r (by revert r; decide), gs r hr]
  have a3 : ∀ r ∈ [Reg.a0, .a2, .a3, .a4, .a5, .a6, .a7], v₃.gpr r = s.gpr r := fun r hr => by
    rw [(o₁.trans (o₂.trans o₃)).get r (by revert r; decide), gs r hr]
  have a4 : ∀ r ∈ [Reg.a0, .a2, .a3, .a4, .a5, .a6, .a7], v₄.gpr r = s.gpr r := fun r hr => by
    rw [(o₁.trans (o₂.trans (o₃.trans o₄))).get r (by revert r; decide), gs r hr]
  refine ⟨⟨by rw [kw.sp, hsp], by rw [kw.wr, kv.wr]; rfl, by rw [kw.mem]; exact hsv⟩, by rw [kw.rd, hrd],
    by rw [ow.get .s0, o₄.get .s0, o₃.get .s0, e₂], ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [ow.get .s1, o₄.get .s1, e₃, a2 .a4 (by decide)]
  · rw [ow.get .s2, e₄, a3 .a0 (by decide)]
  · rw [ew, a4 .a2 (by decide)]
  · rw [kw.gpr r (by revert r; decide), gs r (by revert r; decide)]
  · rw [kw.mem]; exact hm.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp

end

end VG.Proof.RsaOaep.RISCV64.Dec
