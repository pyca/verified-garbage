module

public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Base
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
public import VerifiedGarbage.Impl.RsaPss.RISCV64.Sign
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# RSASSA-PSS signing on RISC-V: the precondition and the entry

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/Pre.lean`, `Sg/Entry.lean`), with the frame of
RSAES-OAEP decryption (`Proof/RsaOaep/RISCV64/Dc/Priv.lean`): `PreS D s`, the
shared contract's precondition (`Spec.RsaPss.signTableContract`, with the stack of
the frames and of `vg_rsa_private_checked`, `stackBytes`), by name
(`preS_of`), for a digest of `D` bytes; the working space `Ss s` and the
values `Base` fixes in `s1`–`s4` (`vS s`: `k`, `out`, `lo` and `salt_len`),
all public; `fits`; `pro_ok`: the saves and the prologue leave our caller's
registers and return address in their slots and the arguments in the
registers that keep them (`Pro`); and `spill_ok`: then `spill` leaves
`Base`, the modulus' first byte in `t1`, and `n`, `e`, `e_len`, `p`, `p_len`
and the mask `c` of `DB`'s top bits in the six words at `scratch + oP`
(`Spilled`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes oRsa save)
open VG.Impl.RsaPss.RISCV64.Sign (privBytes prologue spill oP)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off fx kR fb fr save_ok Saves fb_al stackArgAddr_eq sc_inW sc_in)
open VG.Proof.RsaPss.RISCV64 (loB)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_ld wp_sd wp_mov wp_addSp wp_nil wp_lbu wp_srl wp_or wp_subi
  wp_li wp_sub wp_and)

theorem stackArgs_sixteen (s : State) :
    List.map (stackArg s) (List.range 16) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15] := rfl

/-- The stack the function uses: its frame (`frameBytes`), the private
operation's (`privBytes`) and that function's own. -/
def stackBytes : Nat := frameBytes + privBytes + Impl.Rsa.RISCV64.Priv.frameBytes

theorem stackBytes_eq : stackBytes = 3472 := rfl

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
abbrev pR (s : State) : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
abbrev dgR (D : Nat) (s : State) : Region := ⟨stackArg s 8, D⟩
abbrev sR (s : State) : Region := ⟨stackArg s 10, (stackArg s 11).toNat⟩
abbrev scR (s : State) : Region := ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
abbrev tHR (s : State) : Region := Sig.tableRegion 64 (stackArg s 14) 11
abbrev tGR (s : State) : Region := Sig.tableRegion 64 (stackArg s 15) 5
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 128⟩

/-- The stack the function uses. -/
abbrev kS (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩

/-- What the code needs of `signTableContract.pre`, by name, for a hash
function of `D`-byte digests (the table `hash`'s). -/
structure PreS (D : Nat) (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  sp1 : stackBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 128 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, pR s, qR s, dpR s, dqR s, qiR s, dgR D s, sR s, tHR s, tGR s, aR s]
  hwr : s.wr = [oR s, scR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  odg : (oR s).Disjoint (dgR D s)
  osl : (oR s).Disjoint (sR s)
  os : (oR s).Disjoint (scR s)
  oth : (oR s).Disjoint (tHR s)
  otg : (oR s).Disjoint (tGR s)
  oa : (oR s).Disjoint (aR s)
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ps : (pR s).Disjoint (scR s)
  qs : (qR s).Disjoint (scR s)
  dps : (dpR s).Disjoint (scR s)
  dqs : (dqR s).Disjoint (scR s)
  qis : (qiR s).Disjoint (scR s)
  dgs : (dgR D s).Disjoint (scR s)
  sls : (sR s).Disjoint (scR s)
  sth : (scR s).Disjoint (tHR s)
  stg : (scR s).Disjoint (tGR s)
  sa : (scR s).Disjoint (aR s)
  ko : (kS s).Disjoint (oR s)
  kn : (kS s).Disjoint (nR s)
  ke : (kS s).Disjoint (eR s)
  kp : (kS s).Disjoint (pR s)
  kq : (kS s).Disjoint (qR s)
  kdp : (kS s).Disjoint (dpR s)
  kdq : (kS s).Disjoint (dqR s)
  kqi : (kS s).Disjoint (qiR s)
  kdg : (kS s).Disjoint (dgR D s)
  ksl : (kS s).Disjoint (sR s)
  ks : (kS s).Disjoint (scR s)
  kth : (kS s).Disjoint (tHR s)
  ktg : (kS s).Disjoint (tGR s)
  ka : (kS s).Disjoint (aR s)
  wo : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wn : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  we : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  wp : (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64
  wq : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wdp : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wdq : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wqi : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wdg : (stackArg s 8).toNat + D ≤ 2 ^ 64
  wsl : (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64
  wsc : (stackArg s 12).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64
  wth : (stackArg s 14).toNat + 88 ≤ 2 ^ 64
  wtg : (stackArg s 15).toNat + 40 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a3).toNat
  k2 : (s.gpr .a3).toNat ≤ 1024
  ok : (s.gpr .a1).toNat = (s.gpr .a3).toNat
  e1 : 1 ≤ (s.gpr .a5).toNat
  e2 : (s.gpr .a5).toNat ≤ (s.gpr .a3).toNat
  p1 : 1 ≤ (s.gpr .a7).toNat
  p2 : (s.gpr .a7).toNat < (s.gpr .a3).toNat
  q1 : 1 ≤ (stackArg s 1).toNat
  q2 : (stackArg s 1).toNat < (s.gpr .a3).toNat
  h3 : (stackArg s 3).toNat = (s.gpr .a7).toNat
  h7 : (stackArg s 7).toNat = (s.gpr .a7).toNat
  h5 : (stackArg s 5).toNat = (stackArg s 1).toNat
  hs : Spec.RsaPss.scratchWords (s.gpr .a3).toNat ≤ (stackArg s 13).toNat
  als : (stackArg s 12).toNat % 8 = 0
  al14 : (stackArg s 14).toNat % 8 = 0
  al15 : (stackArg s 15).toNat % 8 = 0

/-- The contract, with the hash function one of the tables `tsH` of `MdHash`
and MGF1's one of the tables `tsG` of `Hash`, and the stack of the frames and
of `vg_rsa_private_checked`. -/
abbrev signSpec (tsH tsG : List FnTable) : Contract isa :=
  Spec.RsaPss.signTableContract (abi.withTables Spec.RsaPss.signTableSig [("hash", tsH), ("mgf1", tsG)])
    stackBytes

/-- Unfolds the precondition at `h`. -/
macro "sign_pre" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes = 3471 + 1 := rfl
  unfold signSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns,
    Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_sixteen, List.append_eq, List.range, List.range.loop,
    Spec.Rsa.lenValid] at $h:ident
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns,
    Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_sixteen, List.append_eq, List.range, List.range.loop,
    Spec.Rsa.lenValid] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

theorem preS_of {H : Spec.Mgf1.Hash} {tsH tsG : List FnTable} {s : State} (h : (signSpec tsH tsG).pre s)
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some H) : PreS H.len s := by
  sign_pre at h
  obtain ⟨spal, sp1, sp2, -, -, -, hrd, hwr, on, oe, op, oq, odp, odq, oqi, odg, osl, os, oth, otg, oa, ns, es, ps,
    qs, dps, dqs, qis, dgs, sls, sth, stg, sa, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, kth, ktg, ka, wo, wn,
    we, wp, wq, wdp, wdq, wqi, wdg, wsl, wsc, wth, wtg, k1, k2, ok, e1, e2, p1, p2, q1, q2, h3, h7, h5, hs, hl, als,
    al14, al15⟩ := h
  have hl := hl H hH
  rw [hl] at hrd odg dgs kdg wdg
  exact ⟨spal, sp1, sp2, hrd, hwr, on, oe, op, oq, odp, odq, oqi, odg, osl, os, oth, otg, oa, ns, es, ps, qs, dps,
    dqs, qis, dgs, sls, sth, stg, sa, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, kth, ktg, ka, wo, wn, we, wp,
    wq, wdp, wdq, wqi, wdg, wsl, wsc, wth, wtg, k1, k2, ok, e1, e2, p1, p2, q1, q2, h3, h7, h5, hs, als, al14, al15⟩

/-- The tables, as the contract gives them: the hash function's one of `tsH`
at the stack argument 14 and MGF1's one of `tsG` at 15, with the functions of
distinct names at distinct addresses. -/
theorem spec_tabS {tsH tsG : List FnTable} {s : State} (h : (signSpec tsH tsG).pre s) :
    (∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s T)) ∧
      (∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      ((tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  sign_pre at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-! ## The working space and the registers the code keeps -/

/-- The working space. -/
abbrev Ss (s : State) : Addr := stackArg s 12

/-- `k`. -/
abbrev kk (s : State) : Nat := (s.gpr .a3).toNat

/-- The modulus' first byte, zero-extended. -/
def n0S (s : State) : BitVec 64 := (s.mem (s.gpr .a2)).setWidth 64

/-- `lo` of the modulus' first byte: 1 if `emLen = k - 1`. -/
abbrev loS (s : State) : BitVec 64 := loB (s.mem (s.gpr .a2))

/-- The values `Base` fixes in `s1`–`s4`: `k`, `out`, `lo` and `salt_len`. -/
def vS (s : State) : Reg → BitVec 64
  | .s1 => s.gpr .a3
  | .s2 => s.gpr .a0
  | .s3 => loS s
  | .s4 => stackArg s 11
  | _ => 0

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

theorem scLen : oRsa ≤ (stackArg s 13).toNat * 8 := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; unfold oRsa; omega

theorem sc_sub : Region.Sub (SC Ss s) (scR s) := Region.sub_prefix (scLen P)

omit P in
theorem kR_sub : Region.Sub (kR s) (kS s) := below_sub (by rw [stackBytes_eq]; decide) (by rw [stackBytes_eq]; decide)

/-- `Fits` for the entry state. -/
theorem fits : Fits Ss s where
  sp1 := by have := P.sp1; rw [stackBytes_eq] at this; unfold Proof.RsaOaep.RISCV64.stackBytes; omega
  sp16 := P.spal
  sc := ⟨scR s, by rw [P.hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl, scLen P⟩
  ksc := (P.ks.sub_left kR_sub).sub_right (sc_sub P)
  wS := by show (stackArg s 12).toNat + oRsa ≤ 2 ^ 64; have := P.wsc; have := scLen P; omega

end

section
variable {s t : State} (h : Base Ss vS s t)
include h

theorem Base.sk : t.gpr .s1 = s.gpr .a3 := h.vs .s1 (by decide)
theorem Base.sout : t.gpr .s2 = s.gpr .a0 := h.vs .s2 (by decide)
theorem Base.slo : t.gpr .s3 = loS s := h.vs .s3 (by decide)
theorem Base.ssl : t.gpr .s4 = stackArg s 11 := h.vs .s4 (by decide)

end

/-! ## The entry -/

/-- The stack arguments are in `aR`. -/
theorem in_aR {s : State} {j : Nat} (hj : j < 16) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-- `n`, `e`, `e_len`, `p`, `p_len` and the mask `c` in the six words at `scratch + oP`. -/
structure Spilled (s : State) (m : Mem) : Prop where
  n : m.readW (off (Ss s) oP) 64 = s.gpr .a2
  e : m.readW (off (Ss s) (oP + 8)) 64 = s.gpr .a4
  el : m.readW (off (Ss s) (oP + 16)) 64 = s.gpr .a5
  p : m.readW (off (Ss s) (oP + 24)) 64 = s.gpr .a6
  pl : m.readW (off (Ss s) (oP + 32)) 64 = s.gpr .a7
  c : m.readW (off (Ss s) (oP + 40)) 64 = Proof.RsaPss.RISCV64.cmB (s.mem (s.gpr .a2))

/-- After the saves and the prologue. -/
structure Entered (s t : State) : Prop where
  base : Base Ss vS s t
  t1 : t.gpr .t1 = n0S s
  sp : Spilled s t.mem

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

theorem arg_al {j : Nat} (hj : j < 16) : (stackArgAddr s j).toNat % 8 = 0 := by
  have := P.spal; have := P.sp2
  have e : (stackArgAddr s j).toNat = s.sp.toNat + 8 * j := by
    simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e]; omega

theorem fb_al8 : (fb s).toNat % 8 = 0 := by
  have := fb_al (fits P); omega

theorem oP_al (j : Nat) : (off (Ss s) (oP + 8 * j)).toNat % 8 = 0 := by
  have := P.als
  have e : (off (stackArg s 12) (oP + 8 * j)).toNat = (stackArg s 12).toNat + (oP + 8 * j) % 2 ^ 64 ∨
      (off (stackArg s 12) (oP + 8 * j)).toNat = ((stackArg s 12).toNat + (oP + 8 * j) % 2 ^ 64) - 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  show (off (stackArg s 12) (oP + 8 * j)).toNat % 8 = 0
  unfold oP at *; omega

/-- A load of our stack argument `j` through `t6`, the entry stack pointer,
with memory changed only in the stack and our part of the working space. -/
theorem wp_arg {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 16)
    (h6 : t.gpr .t6 = s.sp) (hrd : t.rd = s.rd) (hm : Frame [kR s, SC Ss s] s.mem t.mem)
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

end

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

omit P in
theorem sc_c8 (j : Nat) (hj : j < 6) : (SC Ss s).Contains (off (Ss s) (oP + 8 * j)) (64 / 8) :=
  Offset.contains_base (Ss s) (by unfold oP oRsa; omega) (by unfold oP; omega)

/-- After the saves and the prologue. -/
structure Pro (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  s0 : t.gpr .s0 = Ss s
  s1 : t.gpr .s1 = s.gpr .a3
  s2 : t.gpr .s2 = s.gpr .a0
  s4 : t.gpr .s4 = stackArg s 11
  args : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], t.gpr r = s.gpr r
  mem : Frame [kR s, SC Ss s] s.mem t.mem

theorem pro_ok : WP isa (.block (save ++ prologue)) (allocd frameBytes s) (Pro s) := by
  refine save_ok (u := allocd frameBytes s) rfl rfl (fb_al8 P) (Frame.refl _ _) (fun r _ => rfl)
    fun v kv h0 hm hsv => ?_
  have hrd : v.rd = s.rd := kv.rd
  have hsp : v.sp = fb s := kv.sp
  have hm2 : Frame [kR s, SC Ss s] s.mem v.mem := hm.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  have gs : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r (by revert r; decide)]; rfl
  simp only [prologue, Impl.RsaOaep.RISCV64.argBase]
  refine wp_addSp fun v₁ o₁ e₁ => ?_
  have g6 : v₁.gpr .t6 = s.sp := by rw [e₁, hsp, BitVec.sub_add_cancel]
  refine wp_arg P (j := 12) (by decide) g6 (o₁.rd.trans hrd) (by rw [o₁.mem]; exact hm2) fun v₂ o₂ e₂ => ?_
  refine wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ => ?_
  refine wp_arg P (j := 11) (by decide) (by rw [o₄.get .t6, o₃.get .t6, o₂.get .t6, g6])
    (by rw [o₄.rd, o₃.rd, o₂.rd, o₁.rd, hrd]) (by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem]; exact hm2)
    fun v₅ o₅ e₅ => wp_nil ?_
  have k₅ : Only [.t6, .s0, .s1, .s2, .s4] v v₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have sv0 : Saves s v := ⟨hsp, by rw [kv.wr]; rfl, hsv⟩
  exact ⟨sv0.keep k₅.keep (R := []) (by rw [k₅.mem]; exact Frame.refl _ _) (by simp), by rw [k₅.rd, hrd],
    by rw [o₅.get .s0, o₄.get .s0, o₃.get .s0, e₂],
    by rw [o₅.get .s1, o₄.get .s1, e₃, o₂.get .a3, o₁.get .a3, gs .a3 (by decide)],
    by rw [o₅.get .s2, e₄, o₃.get .a0, o₂.get .a0, o₁.get .a0, gs .a0 (by decide)], e₅,
    fun r hr => by rw [k₅.gpr r (by revert r; decide), gs r hr], by rw [k₅.mem]; exact hm2⟩

theorem spill_ok {v₅ : State} (E : Pro s v₅) : WP isa (.block spill) v₅ (Entered s) := by
  have F := fits P
  have hrd : v₅.rd = s.rd := E.rd
  have hm2 : Frame [kR s, SC Ss s] s.mem v₅.mem := E.mem
  have a5 := E.args
  have g0 : v₅.gpr .s0 = Ss s := E.s0
  simp only [spill, Impl.RsaPss.RISCV64.Sign.smear, Impl.RsaPss.RISCV64.Sign.cMask, List.cons_append,
    List.nil_append]
  have w8 : ∀ {u : State} (j : Nat), u.wr = v₅.wr → j < 6 → InRegions u.wr (off (Ss s) (oP + 8 * j)) 8 :=
    fun j hu hj => by
      rw [hu, E.sv.wr]; exact sc_inW F (by unfold oP oRsa; omega)
  refine wp_sd (a := off (Ss s) oP) (by rw [g0]) (by simpa using oP_al P 0) (by simpa using w8 0 rfl (by decide))
    fun v₆ m₆ => ?_
  refine wp_sd (a := off (Ss s) (oP + 8)) (by rw [m₆.gpr, g0]) (oP_al P 1) (w8 1 m₆.wr (by decide))
    fun v₇ m₇ => ?_
  refine wp_sd (a := off (Ss s) (oP + 16)) (by rw [m₇.gpr, m₆.gpr, g0]) (oP_al P 2)
    (w8 2 (m₇.wr.trans m₆.wr) (by decide)) fun v₈ m₈ => ?_
  refine wp_sd (a := off (Ss s) (oP + 24)) (by rw [m₈.gpr, m₇.gpr, m₆.gpr, g0]) (oP_al P 3)
    (w8 3 (m₈.wr.trans (m₇.wr.trans m₆.wr)) (by decide)) fun v₉ m₉ => ?_
  refine wp_sd (a := off (Ss s) (oP + 32)) (by rw [m₉.gpr, m₈.gpr, m₇.gpr, m₆.gpr, g0]) (oP_al P 4)
    (w8 4 (m₉.wr.trans (m₈.wr.trans (m₇.wr.trans m₆.wr))) (by decide)) fun v₁₀ m₁₀ => ?_
  have kg : v₁₀.gpr = v₅.gpr := by rw [m₁₀.gpr, m₉.gpr, m₈.gpr, m₇.gpr, m₆.gpr]
  have hn : nR s ∈ s.rd := by rw [P.hrd]; simp
  have hc : (nR s).Contains (s.gpr .a2) 1 := by
    have := Offset.contains_base (s.gpr .a2) (d := 0) (n := 1) (k := (s.gpr .a3).toNat) (by have := P.k1; omega)
      (by decide)
    simpa only [BitVec.add_zero] using this
  have hf1 : Frame [SC Ss s] v₅.mem v₁₀.mem := by
    rw [m₁₀.mem, m₉.mem, m₈.mem, m₇.mem, m₆.mem]
    have hS : SC Ss s ∈ [SC Ss s] := List.mem_singleton_self _
    exact (((((Frame.refl _ _).writeW hS _ (by simpa using sc_c8 0 (by decide))).writeW hS _
      (sc_c8 1 (by decide))).writeW hS _ (sc_c8 2 (by decide))).writeW hS _ (sc_c8 3 (by decide))).writeW hS _
      (sc_c8 4 (by decide))
  have hf : Frame [kR s, SC Ss s] s.mem v₁₀.mem := hm2.trans (hf1.mono (by simp))
  refine wp_lbu (a := s.gpr .a2) (by rw [kg, a5 .a2 (by decide), BitVec.add_zero])
    (by rw [m₁₀.rd, m₉.rd, m₈.rd, m₇.rd, m₆.rd, hrd]; exact ⟨nR s, List.mem_append_left _ hn, hc⟩)
    fun v₁₁ o₁₁ e₁₁ => ?_
  refine wp_srl fun v₁₂ o₁₂ e₁₂ => wp_srl fun v₁₃ o₁₃ e₁₃ => wp_or fun v₁₄ o₁₄ e₁₄ => wp_srl fun v₁₅ o₁₅ e₁₅ =>
    wp_or fun v₁₆ o₁₆ e₁₆ => wp_srl fun v₁₇ o₁₇ e₁₇ => wp_or fun v₁₈ o₁₈ e₁₈ =>
    wp_subi (imm := 1) fun v₁₉ o₁₉ e₁₉ => wp_srl fun w ow ew => ?_
  have hb : v₁₁.gpr .t1 = n0S s := by
    rw [e₁₁]
    show (v₁₀.mem (s.gpr .a2)).setWidth 64 = (s.mem (s.gpr .a2)).setWidth 64
    rw [hf _ fun r hr hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (P.kn.sub_left kR_sub) _ hx hc
      · exact (P.ns.sub_right (sc_sub P)).symm _ hx hc]
  have m18 : v₁₈.gpr .t2 = Proof.RsaPss.RISCV64.smB (s.mem (s.gpr .a2)) := by
    rw [e₁₈, o₁₇.get .t2, e₁₇, e₁₆, o₁₅.get .t2, e₁₅, e₁₄, o₁₃.get .t2, e₁₃, e₁₂, hb]; rfl
  have m20 : w.gpr .s3 = loS s := by rw [ew, e₁₉, m18]; rfl
  -- The mask `c`.
  refine wp_li (imm := 0) (by decide) fun y₁ p₁ f₁ => wp_sub fun y₂ p₂ f₂ =>
    wp_li (imm := 0xFF) (by decide) fun y₃ p₃ f₃ => wp_and fun y₄ p₄ f₄ => wp_or fun y₅ p₅ f₅ => ?_
  have kw : Only [.t1, .t2, .t3, .s3, .t4] v₁₀ y₅ :=
    (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans (o₁₇.trans (o₁₈.trans (o₁₉.trans (ow.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))))))))))))).mono
  have c5 : y₅.gpr .t2 = Proof.RsaPss.RISCV64.cmB (s.mem (s.gpr .a2)) := by
    rw [f₅, p₄.get .t2, p₃.get .t2, p₂.get .t2, p₁.get .t2, ow.get .t2, o₁₉.get .t2, m18, f₄, p₃.get .t3, f₂,
      f₁, p₁.get .s3, m20, f₃]; rfl
  refine wp_sd (a := off (Ss s) (oP + 40)) (by rw [kw.get .s0, kg, g0]) (oP_al P 5)
    (w8 5 (by rw [kw.wr, m₁₀.wr, m₉.wr, m₈.wr, m₇.wr, m₆.wr]) (by decide)) fun y m => wp_nil ?_
  have hm : y.mem = v₁₀.mem.writeW (off (Ss s) (oP + 40)) (Proof.RsaPss.RISCV64.cmB (s.mem (s.gpr .a2))) := by
    rw [m.mem, c5, kw.mem]
  have kK : Kept [.t1, .t2, .t3, .s3, .t4] v₅ y :=
    (m₆.keep.trans (m₇.keep.trans (m₈.keep.trans (m₉.keep.trans (m₁₀.keep.trans
      (kw.keep.trans m.keep)))))).mono
  have hS : SC Ss s ∈ [SC Ss s] := List.mem_singleton_self _
  have hfy : Frame [SC Ss s] v₅.mem y.mem := by rw [hm]; exact hf1.writeW hS _ (sc_c8 5 (by decide))
  have sv : Saves s y := E.sv.keep kK hfy fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Proof.RsaOaep.RISCV64.slR_sc F
  have hfa : Frame [kR s, SC Ss s] s.mem y.mem := hm2.trans (hfy.mono (by simp))
  have sp : Spilled s y.mem := by
    rw [hm, m₁₀.mem, m₉.mem, m₈.mem, m₇.mem, m₆.mem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_self64, a5 .a2 (by decide)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_self64, m₆.gpr, a5 .a4 (by decide)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_self64, m₇.gpr, m₆.gpr, a5 .a5 (by decide)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_self64, m₈.gpr, m₇.gpr, m₆.gpr, a5 .a6 (by decide)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega)) (by unfold oP; omega) (by unfold oP; omega)) (by decide),
        Mem.readW_writeW_self64, m₉.gpr, m₈.gpr, m₇.gpr, m₆.gpr, a5 .a7 (by decide)]
    · rw [Mem.readW_writeW_self64]
  refine ⟨⟨sv, by rw [m.rd, kw.rd, m₁₀.rd, m₉.rd, m₈.rd, m₇.rd, m₆.rd, hrd],
    by rw [m.gpr, kw.get .s0, kg, g0], fun r hr => ?_, hfa⟩,
    by rw [m.gpr, (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans (o₁₇.trans (o₁₈.trans (o₁₉.trans
      (ow.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅))))))))))))).get .t1, hb], sp⟩
  simp only [Proof.RsaOaep.RISCV64.fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [vS] <;> rw [m.gpr]
  · rw [kw.get .s1, kg]; exact E.s1
  · rw [kw.get .s2, kg]; exact E.s2
  · rw [p₅.get .s3, p₄.get .s3, p₃.get .s3, p₂.get .s3, p₁.get .s3]; exact m20
  · rw [kw.get .s4, kg]; exact E.s4

end

end VG.Proof.RsaPss.RISCV64.Sg
