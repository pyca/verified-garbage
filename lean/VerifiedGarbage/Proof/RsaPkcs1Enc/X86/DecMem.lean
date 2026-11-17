module

import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `RsaPkcs1Enc.X86.DecBase`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on x86: where everything is

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecBase.lean`): `EP`, what two runs
share (the frame's base `B`, the pointers, the lengths, and the public key's
bytes `nB` and `eB`), and its layout (`EP.lay`,
`Proof/RsaPkcs1Sig/X86/Lay.lean`), with the 3448 bytes below the frame that
the private-key operation and its return address use. `In P σ`: the state
`σ` the body starts from; `S P σ s`: a state of the body. The shared
contract, with the stack of the frames and of the calls, gives
`In (ep s) (entered frameBytes s)` (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  ml : BitVec 32
  n : BitVec 32
  e : BitVec 32
  d : BitVec 32
  inp : BitVec 32
  p : BitVec 32
  q : BitVec 32
  dp : BitVec 32
  dq : BitVec 32
  qinv : BitVec 32
  scr : BitVec 32
  K : Nat
  el : Nat
  dl : Nat
  pl : Nat
  ql : Nat
  sl : Nat
  nB : List Byte
  eB : List Byte

namespace EP

variable (P : EP)

abbrev OUT : Region := ⟨P.out.setWidth 64, P.K⟩
abbrev ML : Region := ⟨P.ml.setWidth 64, 8⟩
abbrev N : Region := ⟨P.n.setWidth 64, P.K⟩
abbrev E : Region := ⟨P.e.setWidth 64, P.el⟩
abbrev D : Region := ⟨P.d.setWidth 64, P.dl⟩
abbrev INP : Region := ⟨P.inp.setWidth 64, P.K⟩
abbrev PP : Region := ⟨P.p.setWidth 64, P.pl⟩
abbrev QQ : Region := ⟨P.q.setWidth 64, P.ql⟩
abbrev DP : Region := ⟨P.dp.setWidth 64, P.pl⟩
abbrev DQ : Region := ⟨P.dq.setWidth 64, P.ql⟩
abbrev QI : Region := ⟨P.qinv.setWidth 64, P.pl⟩
abbrev SCR : Region := ⟨P.scr.setWidth 64, P.sl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.ml, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.d,
    BitVec.ofNat 32 P.dl, P.inp, BitVec.ofNat 32 P.K, P.p, BitVec.ofNat 32 P.pl, P.q, BitVec.ofNat 32 P.ql,
    P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl, P.scr,
    BitVec.ofNat 32 P.sl]

abbrev ro : List Region := [P.N, P.E, P.D, P.INP, P.PP, P.QQ, P.DP, P.DQ, P.QI]
abbrev rw : List Region := [P.OUT, P.ML, P.SCR]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  argv := P.argv
  ro := P.ro
  rw := P.rw
  C := 3448

end EP

/-- The state the body starts from. -/
structure In (P : EP) (σ : State) : Prop where
  ok : P.lay.Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  dl1 : 1 ≤ P.dl
  dlK : P.dl ≤ P.K
  pl1 : 1 ≤ P.pl
  plK : P.pl < P.K
  ql1 : 1 ≤ P.ql
  qlK : P.ql < P.K
  slK : Spec.Rsa.scratchWords P.K ≤ P.sl
  sl32 : P.sl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (P.n.setWidth 64) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (P.e.setWidth 64) P.el = P.eB

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In P σ ∧ P.lay.St σ s

namespace In

variable {P : EP} {σ : State} (h : In P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the calls'. -/
abbrev stackBytes : Nat := 16 + frameBytes + 3448

/-- The shared contract, with that stack. -/
abbrev spec : Contract isa := Spec.RsaPkcs1Enc.decryptContract abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes
  out := arg s 0
  ml := arg s 2
  n := arg s 3
  e := arg s 5
  d := arg s 7
  inp := arg s 9
  p := arg s 11
  q := arg s 13
  dp := arg s 15
  dq := arg s 17
  qinv := arg s 19
  scr := arg s 21
  K := (arg s 4).toNat
  el := (arg s 6).toNat
  dl := (arg s 8).toNat
  pl := (arg s 12).toNat
  ql := (arg s 14).toNat
  sl := (arg s 22).toNat
  nB := Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat
  eB := Spec.Rsa.bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes (ep s).argv (ep s).ro (ep s).rw s 3448 := rfl

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  -- The lengths the contract states equal, rewritten in the precondition before it is split: a rewrite
  -- of a fact among the hundred it splits into replaces the fact in a context of that size.
  obtain ⟨olk, ilk, dpl, qil, dql⟩ : (arg s 1).toNat = (arg s 4).toNat ∧ (arg s 10).toNat = (arg s 4).toNat ∧
      (arg s 16).toNat = (arg s 12).toNat ∧ (arg s 20).toNat = (arg s 12).toNat ∧
      (arg s 18).toNat = (arg s 14).toNat := by
    sig_split h
    rename_i hsp hsa hrd hwr oM oN oE oD oI oP oQ oDP oDQ oQI oS oA mN mE mD mI mP mQ mDP mDQ mQI mS mA nS nA
      eS eA dS dA iS iA pS pA qS qA dpS dpA dqS dqA qiS qiA sA rO rM rN rE rD rI rP rQ rDP rDQ rQI rS rA kO kM
      kN kE kD kI kP kQ kDP kDQ kQI kS kA fO fM fN fE fD fI fP fQ fDP fDQ fQI fS kv olk ilk el1 elK dl1 dlK
      pl1 plK ql1 qlK dpl qil dql
    exact ⟨olk, ilk, dpl, qil, dql⟩
  have a1 : arg s 1 = arg s 4 := BitVec.eq_of_toNat_eq olk
  have a10 : arg s 10 = arg s 4 := BitVec.eq_of_toNat_eq ilk
  have a16 : arg s 16 = arg s 12 := BitVec.eq_of_toNat_eq dpl
  have a20 : arg s 20 = arg s 12 := BitVec.eq_of_toNat_eq qil
  have a18 : arg s 18 = arg s 14 := BitVec.eq_of_toNat_eq dql
  rw [olk, ilk, dpl, qil, dql] at h
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at h
  sig_split h
  rename_i hsp hsa hrd hwr oM oN oE oD oI oP oQ oDP oDQ oQI oS oA mN mE mD mI mP mQ mDP mDQ mQI mS mA nS nA
    eS eA dS dA iS iA pS pA qS qA dpS dpA dqS dqA qiS qiA sA rO rM rN rE rD rI rP rQ rDP rDQ rQI rS rA kO kM
    kN kE kD kI kP kQ kDP kDQ kQI kS kA fO fM fN fE fD fI fP fQ fDP fDQ fQI fS kv _ _ el1 elK dl1 dlK
    pl1 plK ql1 qlK _ _ _
  have slK := h
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega_arith
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 3568, 3568⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  have sl32 : (arg s 22).toNat < 2 ^ 32 := (arg s 22).isLt
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, dl1 := dl1, dlK := dlK, pl1 := pl1, plK := plK, ql1 := ql1,
      qlK := qlK, slK := slK, sl32 := sl32
      nB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below16).symm)
        (by show (arg s 4).toNat ≤ 2 ^ 64; omega_arith)
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 6).toNat ≤ 2 ^ 64; omega_arith) }
  rw [ep_lay]
  refine ok_entered (S := 3568) rfl (by decide) hsp (by simp) (by simp; omega_arith) hrd
    (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kD, kI, kP, kQ, kDP, kDQ, kQI, kO, kM, kS]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [rO, rM, rS]
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oA, mN, mE, mD, mI, mP, mQ, mDP, mDQ, mQI, mA,
      nS.symm, eS.symm, dS.symm, iS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, sA]
  · refine List.Pairwise.cons ?_ (List.pairwise_pair.mpr mS)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [oM, oS]
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 3).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 5).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 7).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 9).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 11).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 13).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 15).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 17).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 19).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 21).isLt; omega_arith)]; omega_arith)
  · simp only [ep, EP.argv, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
      Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, List.getD_cons_zero,
      List.getD_cons_succ, BitVec.ofNat_toNat, BitVec.setWidth_eq, a1, a10, a16, a18, a20, and_self]

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end

/-!
# RSAES-PKCS1-v1_5 decryption on x86: `scratch`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecPrf.lean`): the parts of `scratch`
the function uses (`sc P o n`, its `n` bytes from offset `o`, all within its
first 8448 bytes, which every `scratch` has), and where they are: apart from
each other as their offsets say (`sc_sep`), from the frames and the stack
below (`In.fr_sc`, `In.low_sc`), and from the other buffers (`In.sc_ro`,
`In.sc_out`, `In.sc_ml`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

variable {P : EP} {σ : State}

/-- The `n` bytes of `scratch` from offset `o`. -/
abbrev sc (P : EP) (o n : Nat) : Region := ⟨P.scr.setWidth 64 + BitVec.ofNat 64 o, n⟩

namespace In

variable (h : In P σ)
include h

theorem sl8 : 8448 ≤ P.sl * 8 := by
  have := h.slK; have := h.k64; simp only [Spec.Rsa.scratchWords] at *; omega_arith

theorem scr_fit : P.scr.toNat + P.sl * 8 ≤ 2 ^ 32 := by
  have := h.ok.fits P.SCR (by simp)
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega_using [])] at this

theorem scr_toNat {o : Nat} (ho : o < 8448) : (P.scr + BitVec.ofNat 32 o).toNat = P.scr.toNat + o := by
  have := h.scr_fit; have := h.sl8
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho]), Nat.mod_eq_of_lt (by omega_arith)]

/-- `scratch + o`, as an address. -/
theorem scrA {o : Nat} (ho : o < 8448) :
    (P.scr + BitVec.ofNat 32 o).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 o := by
  have := h.scr_fit; have := h.sl8
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h.scr_toNat ho, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := P.scr.toNat) (by have := P.scr.isLt; omega_using []), Nat.mod_eq_of_lt (a := o) (by omega_using [ho])]

/-- `[scratch + o + d]`, as an address. -/
theorem addrSc {o d : Nat} (ho : o + d < 8448) :
    addr (P.scr + BitVec.ofNat 32 o) d = P.scr.setWidth 64 + BitVec.ofNat 64 (o + d) := by
  rw [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, h.scrA ho]

theorem sc_sub {o n : Nat} (hn : o + n ≤ 8448) : Region.Sub (sc P o n) P.SCR :=
  Offset.sub_base _ (by have := h.sl8; omega_using [hn, this])

theorem sc_ro {o n : Nat} (hn : o + n ≤ 8448) {R : Region} (hR : R ∈ P.lay.ro) : (sc P o n).Disjoint R :=
  (h.ok.rw_ro (w := P.SCR) (by simp) hR).sub_left (h.sc_sub hn)

theorem sc_out {o n : Nat} (hn : o + n ≤ 8448) : (sc P o n).Disjoint P.OUT := by
  have := h.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact (this.1.2.symm).sub_left (h.sc_sub hn)

theorem sc_ml {o n : Nat} (hn : o + n ≤ 8448) : (sc P o n).Disjoint P.ML := by
  have := h.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact (this.2.1.symm).sub_left (h.sc_sub hn)

theorem fr_sc {d k o n : Nat} (hd : d + k ≤ frameBytes + 16) (hn : o + n ≤ 8448) :
    Region.Disjoint ⟨P.lay.fr d, k⟩ (sc P o n) :=
  (h.ok.stk_fr (R := P.SCR) (.inr (by simp)) hd).sub_right (h.sc_sub hn)

theorem low_sc {o n : Nat} (hn : o + n ≤ 8448) : P.lay.LOW.Disjoint (sc P o n) :=
  (h.ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right (h.sc_sub hn)

end In

theorem sc_sep {o n o' n' : Nat} (hs : o + n ≤ o' ∨ o' + n' ≤ o) (h₁ : o + n ≤ 8448) (h₂ : o' + n' ≤ 8448) :
    (sc P o n).Disjoint (sc P o' n') :=
  Offset.disjoint _ hs (by omega_using [h₁]) (by omega_using [h₂])

theorem St.sc_w {s : State} (hs : S P σ s) {o n : Nat} (hn : o + n ≤ 8448) :
    InRegions s.wr (P.scr.setWidth 64 + BitVec.ofNat 64 o) n :=
  ⟨P.SCR, hs.2.inRw (by simp), Offset.contains_base _ (by have := hs.1.sl8; omega_using [hn, this]) (by omega_using [hn])⟩

theorem St.sc_r {s : State} (hs : S P σ s) {o n : Nat} (hn : o + n ≤ 8448) :
    InRegions (s.rd ++ s.wr) (P.scr.setWidth 64 + BitVec.ofNat 64 o) n :=
  let ⟨r, hr, hc⟩ := St.sc_w hs hn
  ⟨r, List.mem_append_right _ hr, hc⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
