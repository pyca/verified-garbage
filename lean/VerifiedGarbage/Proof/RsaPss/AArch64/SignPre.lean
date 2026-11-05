module

public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.Impl.RsaPss.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS signing on AArch64: the precondition and the frame

`PreS tsH tsG K s`: the contract's precondition (`signTableContract`, with
the stack `stk K` of the frame and a callee using `K` bytes), by name
(`preS_of`). The frame of `frameBytes` bytes is at `fb s`, below which the
callee uses `K` bytes.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64.Sgn (stackArgs_thirteen)

/-- The stack signing uses: its frame, and its callee's stack. -/
def stk (K : Nat) : Nat := frameBytes + K

/-- The buffers: `out`, `n`, `e`, `p`, `q`, `dP`, `dQ`, `qInv`, the digest,
the salt, the working space, the tables, the arguments on the stack, and the
stack the function uses. -/
abbrev oR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
abbrev pR (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
abbrev dgR (s : State) : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
abbrev slR (s : State) : Region := ⟨stackArg s 10, (stackArg s 11).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
abbrev tHR (s : State) : Region := Sig.tableRegion 64 (stackArg s 14) 11
abbrev tGR (s : State) : Region := Sig.tableRegion 64 (stackArg s 15) 5
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 128⟩
abbrev kR (K : Nat) (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 (stk K), stk K⟩

/-- What the code needs of `signTableContract.pre`, by name, for the tables
`tsH` of `MdHash` and `tsG` of `Hash`. -/
structure PreS (tsH tsG : List FnTable) (K : Nat) (s : State) : Prop where
  sp1 : stk K ≤ s.sp.toNat
  sp2 : s.sp.toNat + 128 ≤ 2 ^ 64
  tabH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s T)
  tabG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)
  hsy : ((tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g
  hrd : Covers [nR s, eR s, pR s, qR s, dpR s, dqR s, qiR s, dgR s, slR s, tHR s, tGR s, aR s] s.rd
  hwo : oR s ∈ s.wr
  hws : sR s ∈ s.wr
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  odg : (oR s).Disjoint (dgR s)
  osl : (oR s).Disjoint (slR s)
  os : (oR s).Disjoint (sR s)
  otH : (oR s).Disjoint (tHR s)
  otG : (oR s).Disjoint (tGR s)
  oa : (oR s).Disjoint (aR s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  ps : (pR s).Disjoint (sR s)
  qs : (qR s).Disjoint (sR s)
  dps : (dpR s).Disjoint (sR s)
  dqs : (dqR s).Disjoint (sR s)
  qis : (qiR s).Disjoint (sR s)
  dgs : (dgR s).Disjoint (sR s)
  sls : (slR s).Disjoint (sR s)
  stH : (sR s).Disjoint (tHR s)
  stG : (sR s).Disjoint (tGR s)
  sa : (sR s).Disjoint (aR s)
  ko : (kR K s).Disjoint (oR s)
  kn : (kR K s).Disjoint (nR s)
  ke : (kR K s).Disjoint (eR s)
  kp : (kR K s).Disjoint (pR s)
  kq : (kR K s).Disjoint (qR s)
  kdp : (kR K s).Disjoint (dpR s)
  kdq : (kR K s).Disjoint (dqR s)
  kqi : (kR K s).Disjoint (qiR s)
  kdg : (kR K s).Disjoint (dgR s)
  ksl : (kR K s).Disjoint (slR s)
  ks : (kR K s).Disjoint (sR s)
  ktH : (kR K s).Disjoint (tHR s)
  ktG : (kR K s).Disjoint (tGR s)
  ka : (kR K s).Disjoint (aR s)
  wo : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  wn : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  we : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64
  wp : (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64
  wq : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wdp : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wdq : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wqi : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wdg : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  wsl : (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64
  ws : (stackArg s 12).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64
  wtH : (stackArg s 14).toNat + 88 ≤ 2 ^ 64
  wtG : (stackArg s 15).toNat + 40 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .x3).toNat
  k2 : (s.gpr .x3).toNat ≤ 1024
  ol : (s.gpr .x1).toNat = (s.gpr .x3).toNat
  e1 : 1 ≤ (s.gpr .x5).toNat
  e2 : (s.gpr .x5).toNat ≤ (s.gpr .x3).toNat
  p1 : 1 ≤ (s.gpr .x7).toNat
  p2 : (s.gpr .x7).toNat < (s.gpr .x3).toNat
  q1 : 1 ≤ (stackArg s 1).toNat
  q2 : (stackArg s 1).toNat < (s.gpr .x3).toNat
  hdp : (stackArg s 3).toNat = (s.gpr .x7).toNat
  hqi : (stackArg s 7).toNat = (s.gpr .x7).toNat
  hdq : (stackArg s 5).toNat = (stackArg s 1).toNat
  hs : 16 * (s.gpr .x3).toNat + 32 + 1024 ≤ (stackArg s 13).toNat
  hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 14) (stackArg s 9)

/-- The ABI the contract states, with the tables. -/
abbrev signAbi (tsH tsG : List FnTable) : Abi isa :=
  abi.withTables Spec.RsaPss.signTableSig [("hash", tsH), ("mgf1", tsG)]

theorem preS_of {tsH tsG : List FnTable} {K : Nat} {s : State}
    (h : (Spec.RsaPss.signTableContract (signAbi tsH tsG) (stk K)).pre s) : PreS tsH tsG K s := by
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e] at h
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param, Spec.HashTable.param,
    Spec.MdHashTable.wordCount, Spec.HashTable.wordCount, Spec.MdHashTable.fns, Spec.HashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    List.append_eq, _root_.List.range, _root_.List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero,
    Option.some.injEq, exists_eq_left'] at h
  sig_split h
  rename_i sp1 sp2 tabH tabG hsy hrd hwr on oe op oq odp odq oqi odg osl os otH otG oa ns es ps qs dps dqs qis dgs
    sls stH stG sa ko kn ke kp kq kdp kdq kqi kdg ksl ks ktH ktG ka wo wn we wp wq wdp wdq wqi wdg wsl ws wtH wtG
    _ob1 ol e1 e2 p1 p2 q1 q2 hdp hqi hdq hs
  obtain ⟨k1, k2⟩ := _ob1
  rw [← e] at sp1 ko kn ke kp kq kdp kdq kqi kdg ksl ks ktH ktG ka
  exact ⟨sp1, sp2, tabH, tabG, hsy, by rw [hrd]; exact Covers.refl _, by rw [hwr]; simp, by rw [hwr]; simp, on, oe,
    op, oq, odp, odq, oqi, odg, osl, os, otH, otG, oa, ns, es, ps, qs, dps, dqs, qis, dgs, sls, stH, stG, sa, ko, kn,
    ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, ktH, ktG, ka, wo, wn, we, wp, wq, wdp, wdq, wqi, wdg, wsl, ws, wtH, wtG,
    k1, k2, ol, e1, e2, p1, p2, q1, q2, hdp, hqi, hdq,
    by unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs; omega, h⟩

/-! ## The frame -/

/-- The frame's base. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The base of the stack the function uses. -/
abbrev kb (K : Nat) (s : State) : Addr := s.sp - BitVec.ofNat 64 (stk K)

theorem fb_eq (K : Nat) (s : State) : fb s = kb K s + BitVec.ofNat 64 K := by
  unfold fb kb
  rw [Offset.sub_ofNat_eq s.sp (show frameBytes ≤ stk K by unfold stk; omega)]
  rw [show stk K - frameBytes = K by unfold stk; omega]

theorem off_fb (K : Nat) (s : State) (d : Nat) :
    fb s + BitVec.ofNat 64 d = kb K s + BitVec.ofNat 64 (K + d) := by
  rw [fb_eq K, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem kb_toNat {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreS tsH tsG K s) :
    (kb K s).toNat + stk K = s.sp.toNat ∧ s.sp.toNat + 104 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor <;> omega

theorem fb_toNat {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreS tsH tsG K s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stk at this; omega

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (K : Nat) (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR K s) := by
  rw [off_fb K]; exact Offset.sub_base _ (by unfold stk; omega)

theorem frame_sub0 (K : Nat) (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (kR K s) := by
  have := frame_sub K s (d := 0) (n := frameBytes) (by omega)
  rwa [BitVec.add_zero] at this

/-- The stack below the frame, which the callee uses. -/
theorem below_fb (K : Nat) (s : State) : below (fb s) K = ⟨kb K s, K⟩ := by
  simp only [below, fb_eq K, BitVec.add_sub_cancel]

theorem below_sub (K : Nat) (s : State) : Region.Sub (below (fb s) K) (kR K s) := by
  rw [below_fb]; exact Region.sub_prefix (by unfold stk; omega)

/-- The stack arguments, from the frame. -/
theorem stackArgAddr_fb (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (frameBytes + 8 * j) := by
  rw [stackArgAddr, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem keep_of_frame {K : Nat} {s : State} {R : Region} (hR : (kR K s).Disjoint R) :
    ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region)], R.Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (hR.sub_left (frame_sub0 K s)).symm

/-- The stack arguments are readable. -/
theorem arg_in {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreS tsH tsG K s) {rs : List Region}
    (hrd : Covers s.rd rs) {j : Nat} (hj : j < 16) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ <| hp.hrd _ _ ⟨aR s, by simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frame {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreS tsH tsG K s) {m : Mem}
    (h : Frame [⟨fb s, frameBytes⟩] s.mem m) {j : Nat} (hj : j < 16) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := aR s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega))
    (keep_of_frame hp.ka) (by decide)

theorem in_frame (s : State) (rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (⟨fb s, frameBytes⟩ :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by unfold frameBytes at h; omega)⟩

theorem saved_offs : ∀ p ∈ saved, 96 ≤ p.2 ∧ p.2 + 8 ≤ 96 + 88 := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

end VG.Proof.RsaPss.AArch64.Sgn
