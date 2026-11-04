module

public import VerifiedGarbage.Spec.RsaOaep.Precomputed
public import VerifiedGarbage.Spec.RsaOaep.Table
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Base
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP encryption on RISC-V: the precondition and the entry

Untrusted: everything here is checked by Lean. `PreO D s`: the contract's
precondition (`Spec.RsaOaep.encryptTableContract`, with the stack of the
frame and of the streaming hash functions, `stackBytes`), by name
(`preO_of`), and what it says of MGF1's table (`spec_tab`). `entry_ok`: from
the state after the allocation, the saves and the prologue leave `Base` with the label in `s6` and `s7`, and `msg`,
`msg_len` and `seed` in `t2`, `t3` and `t4` (`Entered`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_ld wp_mov wp_addSp wp_nil)

theorem stackArgs_seven (s : State) :
    List.map (stackArg s) (List.range 7) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6] := rfl

theorem stackArgs_eight (s : State) :
    List.map (stackArg s) (List.range 8) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

/-- The buffers: `out`, `n`, `e`, the label, the message, the seed, the
working space, the precomputed values, MGF1's table and the arguments on the
stack. -/
abbrev oR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
abbrev lR (s : State) : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
abbrev mR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev sdR (D : Nat) (s : State) : Region := ⟨stackArg s 2, D⟩
abbrev scR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
abbrev pR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
abbrev tR (s : State) : Region := Sig.tableRegion 64 (stackArg s 7) 5
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 64⟩

/-- What the code needs of `encryptTableContract.pre`, by name, for a
hash function of `D`-byte digests. -/
structure PreO (D : Nat) (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  sp1 : stackBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 56 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, lR s, mR s, sdR D s, pR s, tR s, aR s]
  hwr : s.wr = [oR s, scR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  ol : (oR s).Disjoint (lR s)
  om : (oR s).Disjoint (mR s)
  osd : (oR s).Disjoint (sdR D s)
  osc : (oR s).Disjoint (scR s)
  op : (oR s).Disjoint (pR s)
  ot : (oR s).Disjoint (tR s)
  oa : (oR s).Disjoint (aR s)
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ls : (lR s).Disjoint (scR s)
  ms : (mR s).Disjoint (scR s)
  sds : (sdR D s).Disjoint (scR s)
  sp : (scR s).Disjoint (pR s)
  st : (scR s).Disjoint (tR s)
  sa : (scR s).Disjoint (aR s)
  ko : (kR s).Disjoint (oR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kl : (kR s).Disjoint (lR s)
  km : (kR s).Disjoint (mR s)
  ksd : (kR s).Disjoint (sdR D s)
  ksc : (kR s).Disjoint (scR s)
  kp : (kR s).Disjoint (pR s)
  kt : (kR s).Disjoint (tR s)
  ka : (kR s).Disjoint (aR s)
  wo : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wn : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  we : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  wl : (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64
  wm : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wsd : (stackArg s 2).toNat + D ≤ 2 ^ 64
  wsc : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  wt : (stackArg s 7).toNat + 40 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a3).toNat
  k2 : (s.gpr .a3).toNat ≤ 1024
  ok : (s.gpr .a1).toNat = (s.gpr .a3).toNat
  e1 : 1 ≤ (s.gpr .a5).toNat
  e2 : (s.gpr .a5).toNat ≤ (s.gpr .a3).toNat
  hs : Spec.RsaPss.publicScratchWords (s.gpr .a3).toNat ≤ (stackArg s 4).toNat
  hp : (stackArg s 6).toNat = Spec.Rsa.precomputedWords (s.gpr .a3).toNat
  al3 : (stackArg s 3).toNat % 8 = 0
  al5 : (stackArg s 5).toNat % 8 = 0
  al7 : (stackArg s 7).toNat % 8 = 0

/-- The contract, with MGF1's hash function one of the tables `ts`, and the
stack of the frame and of the streaming hash functions. -/
abbrev encSpec (H : Spec.Mgf1.Hash) (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.encryptTableContract H (abi.withTables (Spec.RsaOaep.encryptTableSig H) [("mgf1", ts)]) stackBytes

/-- Unfolds the precondition at `h`. -/
macro "enc_pre" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes = 335 + 1 := rfl
  unfold encSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_eight, List.append_eq, List.range, List.range.loop] at $h:ident
  sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_eight, List.append_eq, List.range, List.range.loop] at $h:ident
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left'] at $h:ident))

theorem preO_of {H : Spec.Mgf1.Hash} {ts : List FnTable} {s : State} (h : (encSpec H ts).pre s) :
    PreO H.len s := by
  enc_pre at h
  obtain ⟨spal, sp1, sp2, -, -, hrd, hwr, on, oe, ol, om, osd, osc, op, ot, oa, ns, es, ls, ms, sds, sp, st, sa, ko,
    kn, ke, kl, km, ksd, ksc, kp, kt, ka, wo, wn, we, wl, wm, wsd, wsc, wp, wt, ⟨k1, k2⟩, ok, e1, e2, hs, hp, al3,
    al5, al7⟩ := h
  exact ⟨spal, sp1, by omega, hrd, hwr, on, oe, ol, om, osd, osc, op, ot, oa, ns, es, ls, ms, sds, sp, st, sa, ko,
    kn, ke, kl, km, ksd, ksc, kp, kt, ka, wo, wn, we, wl, wm, wsd, wsc, wp, wt, k1, k2, ok, e1, e2, hs, hp, al3,
    al5, al7⟩

/-- MGF1's table, as the contract gives it: one of `ts`, at the stack
argument 7, with the functions of distinct names at distinct addresses. -/
theorem spec_tab {H : Spec.Mgf1.Hash} {ts : List FnTable} {s : State} (h : (encSpec H ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s T)) ∧
      (ts.map (fun T : FnTable => T.fns)).flatten.Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  enc_pre at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩

/-- The working space. -/
abbrev S (s : State) : Addr := stackArg s 3

/-- The values `Base` fixes in `s1`–`s4`: `k`, `out`, `e` and its length. -/
def vO (s : State) : Reg → BitVec 64
  | .s1 => s.gpr .a3
  | .s2 => s.gpr .a0
  | .s3 => s.gpr .a4
  | .s4 => s.gpr .a5
  | _ => 0

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

theorem scLen : oRsa ≤ (stackArg s 4).toNat * 8 := by
  have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; unfold oRsa; omega

theorem sc_sub : Region.Sub (SC S s) (scR s) := Region.sub_prefix (scLen P)

theorem scR_contains {o n : Nat} (h : o + n ≤ oRsa) : (scR s).Contains (off (S s) o) n :=
  Offset.contains_base _ (by have := scLen P; omega) (by unfold oRsa at h; omega)

theorem PreO.fits : Fits S s where
  sp1 := P.sp1
  sp16 := P.spal
  sc := ⟨scR s, by rw [P.hwr]; simp, rfl, scLen P⟩
  ksc := P.ksc.sub_right (sc_sub P)
  wS := by show (stackArg s 3).toNat + oRsa ≤ 2 ^ 64; have := P.wsc; have := scLen P; omega

end

section
variable {s t : State} (h : Base S vO s t)
include h

theorem Base.s1 : t.gpr .s1 = s.gpr .a3 := h.vs .s1 (by decide)
theorem Base.s2 : t.gpr .s2 = s.gpr .a0 := h.vs .s2 (by decide)
theorem Base.s3 : t.gpr .s3 = s.gpr .a4 := h.vs .s3 (by decide)
theorem Base.s4 : t.gpr .s4 = s.gpr .a5 := h.vs .s4 (by decide)

end

/-! ## The entry -/

/-- The stack arguments are in `aR`. -/
theorem in_aR {s : State} {j : Nat} (hj : j < 8) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-- After the saves and the prologue. -/
structure Entered (s t : State) : Prop where
  base : Base S vO s t
  s6 : t.gpr .s6 = s.gpr .a6
  s7 : t.gpr .s7 = s.gpr .a7
  t2 : t.gpr .t2 = stackArg s 0
  t3 : t.gpr .t3 = stackArg s 1
  t4 : t.gpr .t4 = stackArg s 2

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

theorem arg_al {j : Nat} (hj : j < 8) : (stackArgAddr s j).toNat % 8 = 0 := by
  have := P.spal; have := P.sp2
  have e : (stackArgAddr s j).toNat = s.sp.toNat + 8 * j := by
    simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e]; omega

theorem fb_al8 : (fb s).toNat % 8 = 0 := by
  have := fb_al (PreO.fits P); omega

/-- A load of our stack argument `j` through `t6`, the entry stack pointer. -/
theorem wp_arg {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 8)
    (h6 : t.gpr .t6 = s.sp) (hrd : t.rd = s.rd) (hm : Frame [kR s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .t6 (8 * j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h6]; rfl) (arg_al P hj) ?_ (fun t' o e => k t' o ?_) ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact P.ka.symm) (by decide)]

theorem entry_ok : WP isa (.block (save ++ prologue)) (allocd frameBytes s) (Entered s) := by
  refine save_ok (u := allocd frameBytes s) rfl rfl (fb_al8 P) (Frame.refl _ _) (fun r _ => rfl) fun v kv h0 hm hsv => ?_
  have hrd : v.rd = s.rd := kv.rd
  have hsp : v.sp = fb s := kv.sp
  simp only [prologue, argBase]
  refine wp_addSp fun v₁ o₁ e₁ => ?_
  have g6 : v₁.gpr .t6 = s.sp := by rw [e₁, hsp, BitVec.sub_add_cancel]
  refine wp_arg P (j := 3) (by decide) g6 (o₁.rd.trans hrd) (by rw [o₁.mem]; exact hm) fun v₂ o₂ e₂ => ?_
  refine wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ => wp_mov fun v₅ o₅ e₅ => wp_mov fun v₆ o₆ e₆ =>
    wp_mov fun v₇ o₇ e₇ => wp_mov fun v₈ o₈ e₈ => ?_
  have k₈ : Only [.s1, .s2, .s3, .s4, .s6, .s7] v₂ v₈ :=
    (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))).mono
  have k₂ : Only [.t6, .s0] v v₂ := (o₁.trans o₂).mono
  have g8 : v₈.gpr .t6 = s.sp := by rw [k₈.get .t6, o₂.get .t6]; exact g6
  have r8 : v₈.rd = s.rd := k₈.rd.trans (k₂.rd.trans hrd)
  have m8 : Frame [kR s] s.mem v₈.mem := by rw [k₈.mem, k₂.mem]; exact hm
  refine wp_arg P (j := 0) (by decide) g8 r8 m8 fun v₉ o₉ e₉ => ?_
  refine wp_arg P (j := 1) (by decide) (by rw [o₉.get .t6]; exact g8) (o₉.rd.trans r8)
    (by rw [o₉.mem]; exact m8) fun v₁₀ o₁₀ e₁₀ => ?_
  refine wp_arg P (j := 2) (by decide) (by rw [o₁₀.get .t6, o₉.get .t6]; exact g8)
    (o₁₀.rd.trans (o₉.rd.trans r8)) (by rw [o₁₀.mem, o₉.mem]; exact m8) fun w ow ew => wp_nil ?_
  have kw : Only [.t2, .t3, .t4] v₈ w := (o₉.trans (o₁₀.trans ow)).mono
  have gs : ∀ r ∈ [Reg.a0, .a3, .a4, .a5, .a6, .a7], v₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.gpr r (by revert r; decide), kv.gpr r (by revert r; decide)]; rfl
  have sv : Saves s w := ⟨by rw [kw.sp, k₈.sp, k₂.sp, hsp], by rw [kw.wr, k₈.wr, k₂.wr, kv.wr]; rfl,
    by rw [kw.mem, k₈.mem, k₂.mem]; exact hsv⟩
  refine ⟨⟨sv, kw.rd.trans r8, ?_, fun r hr => ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kw.get .s0, k₈.get .s0]; exact e₂
  · simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [vO]
    · rw [kw.get .s1, o₈.get .s1, o₇.get .s1, o₆.get .s1, o₅.get .s1, o₄.get .s1, e₃, gs .a3 (by decide)]
    · rw [kw.get .s2, o₈.get .s2, o₇.get .s2, o₆.get .s2, o₅.get .s2, e₄, o₃.get .a0, gs .a0 (by decide)]
    · rw [kw.get .s3, o₈.get .s3, o₇.get .s3, o₆.get .s3, e₅, o₄.get .a4, o₃.get .a4, gs .a4 (by decide)]
    · rw [kw.get .s4, o₈.get .s4, o₇.get .s4, e₆, o₅.get .a5, o₄.get .a5, o₃.get .a5, gs .a5 (by decide)]
  · rw [kw.mem, k₈.mem, k₂.mem]
    exact hm.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  · rw [kw.get .s6, o₈.get .s6, e₇, o₆.get .a6, o₅.get .a6, o₄.get .a6, o₃.get .a6, gs .a6 (by decide)]
  · rw [kw.get .s7, e₈, o₇.get .a7, o₆.get .a7, o₅.get .a7, o₄.get .a7, o₃.get .a7, gs .a7 (by decide)]
  · rw [ow.get .t2, o₁₀.get .t2]; exact e₉
  · rw [ow.get .t3]; exact e₁₀
  · exact ew

end

end VG.Proof.RsaOaep.RISCV64
