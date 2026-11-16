module

public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCArgs
public import VerifiedGarbage.Proof.RsaPss.EncodingContract
import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.Params

/-! ### `RsaPss.AArch64.VerifyCall`, which only this module used -/

section

/-! ### `RsaPss.AArch64.VerifyFrame`, which only this module used -/

section

/-! ### `RsaPss.AArch64.VerifyPre`, which only this module used -/

section

/-!
# RSASSA-PSS verification on AArch64: the precondition

`PreV tsH tsG K s`: what the code needs of the contract's precondition
(`verifyPrecomputedMdTableContract`, with the stack `stk K` of the frame and a
callee using `K` bytes), by name. The frame is that of signing (`Sgn.fb`).
`preV_of` gives it from the contract's precondition.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb frame_sub0 stackArgAddr_eq keep_of_frame)

/-- The buffers: `n`, `e`, the digest, the signature, the working space, the
precomputed values, the tables and the arguments on the stack. -/
abbrev nR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
abbrev dgR (s : State) : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
abbrev sgR (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
abbrev pR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
abbrev tHR (s : State) : Region := Sig.tableRegion 64 (stackArg s 6) 11
abbrev tGR (s : State) : Region := Sig.tableRegion 64 (stackArg s 7) 11
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 64⟩

/-- The ABI the contract states, with the tables. -/
abbrev verifyAbi (tsH tsG : List FnTable) : Abi isa :=
  abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]

/-- What the code needs of `verifyPrecomputedMdTableContract.pre`, by name, for
the tables `tsH` of `MdHash` and `tsG` of `MdHash`. -/
structure PreV (tsH tsG : List FnTable) (K : Nat) (s : State) : Prop where
  sp1 : stk K ≤ s.sp.toNat
  sp2 : s.sp.toNat + 64 ≤ 2 ^ 64
  tabH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s T)
  tabG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s T)
  hsy : ((tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g
  hrd : Covers [nR s, eR s, dgR s, sgR s, pR s, tHR s, tGR s, aR s] s.rd
  hws : sR s ∈ s.wr
  hwr : s.wr = [sR s]
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  dgs : (dgR s).Disjoint (sR s)
  sgs : (sgR s).Disjoint (sR s)
  sP : (sR s).Disjoint (pR s)
  stH : (sR s).Disjoint (tHR s)
  stG : (sR s).Disjoint (tGR s)
  sa : (sR s).Disjoint (aR s)
  kn : (kR K s).Disjoint (nR s)
  ke : (kR K s).Disjoint (eR s)
  kdg : (kR K s).Disjoint (dgR s)
  ksg : (kR K s).Disjoint (sgR s)
  ks : (kR K s).Disjoint (sR s)
  kP : (kR K s).Disjoint (pR s)
  ktH : (kR K s).Disjoint (tHR s)
  ktG : (kR K s).Disjoint (tGR s)
  ka : (kR K s).Disjoint (aR s)
  wn : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  we : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  wdg : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64
  wsg : (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64
  ws : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  wP : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  wtH : (stackArg s 6).toNat + 88 ≤ 2 ^ 64
  wtG : (stackArg s 7).toNat + 88 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .x1).toNat
  k2 : (s.gpr .x1).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .x3).toNat
  e2 : (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat
  sgl : (s.gpr .x7).toNat = (s.gpr .x1).toNat
  hs : 8 * (((s.gpr .x1).toNat + 7) / 8) + 48 + 1024 ≤ (stackArg s 3).toNat
  hl : (stackArg s 5).toNat = Spec.Rsa.precomputedWords (s.gpr .x1).toNat
  hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 6) (s.gpr .x5)

theorem kb_toNat {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) :
    (kb K s).toNat + stk K = s.sp.toNat ∧ s.sp.toNat + 64 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor <;> omega_arith

theorem fb_toNat {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) :
    (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stk at this; omega_using [this]

/-- The stack arguments are readable. -/
theorem arg_in {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) {rs : List Region}
    (hrd : Covers s.rd rs) {j : Nat} (hj : j < 8) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ <| hp.hrd _ _ ⟨aR s, by simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frame {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) {m : Mem}
    (h : Frame [⟨fb s, frameBytes⟩] s.mem m) {j : Nat} (hj : j < 8) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := aR s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
    (keep_of_frame hp.ka) (by decide)

theorem preV_of {tsH tsG : List FnTable} {K : Nat} {s : State}
    (h : (Spec.RsaPss.verifyPrecomputedMdTableContract (verifyAbi tsH tsG) (stk K)).pre s) : PreV tsH tsG K s := by
  obtain e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega_using []
  rw [e] at h
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, _root_.List.range, _root_.List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero,
    Option.some.injEq, exists_eq_left'] at h
  sig_split h
  rename_i sp1 sp2 tabH tabG hsy hrd hwr ns es dgs sgs sP stH stG sa kn ke kdg ksg ks kP ktH ktG ka wn we wdg
    wsg ws wP wtH wtG _ob1 e1 e2 sgl hs hl
  obtain ⟨k1, k2⟩ := _ob1
  rw [← e] at sp1 kn ke kdg ksg ks kP ktH ktG ka
  exact ⟨sp1, sp2, tabH, tabG, hsy, by rw [hrd]; exact Covers.refl _, by rw [hwr]; simp, hwr, ns, es, dgs, sgs, sP,
    stH, stG, sa, kn, ke, kdg, ksg, ks, kP, ktH, ktG, ka, wn, we, wdg, wsg, ws, wP, wtH, wtG, k1, k2, e1, e2, sgl,
    by unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords at hs; omega_using [hs], hl, h⟩

end VG.Proof.RsaPss.AArch64.Vfy

end

end


/-!
# RSASSA-PSS verification on AArch64: the prologue

`prologue_ok`: the callee-saved registers and the arguments in their slots
of the frame (`Fr`), `scratch` in `x20`, `x19` and `x21` set, `k` in `x23`
and `n₀` in `x10` (`AtChk`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil wp_addImm wp_ldrb wp_ldrx)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov wp_movw)
open VG.Proof.RsaPss.AArch64 (off)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb frame_sub0 stackArgAddr_fb in_frame wr_frame)

/-- The argument registers kept in slots of the frame. -/
def regSlots : List (Reg × Nat) := [(.x0, sN), (.x2, sE), (.x3, sEl), (.x4, sDig), (.x6, sOut)]

theorem fits : Spill.Fits (saved ++ regSlots) := by decide

/-- `any_salt_len`, zero-extended from its 32 bits. -/
abbrev anyV (s : State) : BitVec 64 := ((stackArg s 1).setWidth 32).setWidth 64

/-- The frame's slots that the code reads: the saved registers, the
arguments. -/
structure Fr (s : State) (m : Mem) : Prop where
  sv : Spill.Saved (fb s) s.gpr saved m
  rs : Spill.Saved (fb s) s.gpr regSlots m
  sl : m.readW (fb s + BitVec.ofNat 64 sSaltLen) 64 = stackArg s 0
  scr : m.readW (fb s + BitVec.ofNat 64 sScrLen) 64 = stackArg s 3
  any : m.readW (fb s + BitVec.ofNat 64 sAny) 64 = anyV s
  pre : m.readW (fb s + BitVec.ofNat 64 sPre) 64 = stackArg s 4
  preLen : m.readW (fb s + BitVec.ofNat 64 sPreLen) 64 = stackArg s 5

/-- The slots of `Fr`: `[96, 248)`, `[264, 272)` and `[312, 328)` of the
frame. -/
abbrev frA (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 152⟩
abbrev frB (s : State) : Region := ⟨fb s + BitVec.ofNat 64 264, 8⟩
abbrev frC (s : State) : Region := ⟨fb s + BitVec.ofNat 64 312, 16⟩

theorem Fr.frame {s : State} {m m' : Mem} (h : Fr s m) {rs : List Region} (hf : Frame rs m m')
    (hA : ∀ r ∈ rs, (frA s).Disjoint r) (hB : ∀ r ∈ rs, (frB s).Disjoint r) (hC : ∀ r ∈ rs, (frC s).Disjoint r) :
    Fr s m' := by
  obtain hw : ∀ {d : Nat}, (96 ≤ d ∧ d + 8 ≤ 248) → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun hd =>
    hf.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hA r hr).sub_left (Offset.sub _ hd.1 (by omega_arith))) (by decide)
  obtain hc : ∀ {d : Nat}, (312 ≤ d ∧ d + 8 ≤ 328) → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun hd =>
    hf.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hC r hr).sub_left (Offset.sub _ hd.1 (by omega_arith))) (by decide)
  refine ⟨h.sv.frame_in (lo := 96) (n := 152) (by decide) hf hA, fun p hp => ?_, by rw [hw (by decide)]; exact h.sl,
    by rw [hw (by decide)]; exact h.scr,
    by rw [hf.readW (r := frB s) (Region.contains_self _ _) hB (by decide)]; exact h.any,
    by rw [hc (by decide)]; exact h.pre, by rw [hc (by decide)]; exact h.preLen⟩
  rw [hw (by revert p; decide)]
  exact h.rs p hp

/-- Before the checks. -/
structure AtChk (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr
  g : ∀ r, r ∉ [Reg.x9, .x10, .x16, .x19, .x20, .x21, .x23, .x27] → u.gpr r = s.gpr r
  x10 : u.gpr .x10 = (s.mem (s.gpr .x0)).setWidth 64
  x19 : u.gpr .x19 = off (stackArg s 2) oSt
  x20 : u.gpr .x20 = stackArg s 2
  x21 : u.gpr .x21 = off (stackArg s 2) oDig
  x27 : u.gpr .x27 = s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64
  x23 : u.gpr .x23 = s.gpr .x1
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem u.mem
  fr : Fr s u.mem

theorem prologue_ok {tsH tsG : List FnTable} {K : Nat} {s u : State} (hp : PreV tsH tsG K s) (hsp0 : u.sp = fb s)
    (hrd0 : u.rd = s.rd) (hwr0 : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm0 : u.mem = s.mem)
    (hg0 : ∀ r, u.gpr r = s.gpr r)
    (hv0 : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block (verifyPrologue ++ n0 .x0)) u (AtChk s) := by
  unfold verifyPrologue save regsUp n0 arg
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  refine wp_ldrSp (by decide) (by
    rw [hsp0, ← stackArgAddr_fb, hrd0]; exact arg_in hp (Covers.left (Covers.refl _)) (j := 6) (by decide))
    fun u₀ o₀ e₀ => ?_
  rw [hsp0, ← stackArgAddr_fb, hm0] at e₀
  obtain hsp : u₀.sp = fb s := o₀.sp.trans hsp0
  obtain hrd : u₀.rd = s.rd := o₀.rd.trans hrd0
  obtain hwr : u₀.wr = ⟨fb s, frameBytes⟩ :: s.wr := o₀.wr.trans hwr0
  obtain hm : u₀.mem = s.mem := o₀.mem.trans hm0
  obtain hg : ∀ r, r ≠ .x10 → u₀.gpr r = s.gpr r := fun r h => (o₀.gpr r (by simpa using h)).trans (hg0 r)
  obtain hv : ∀ r ∈ preservedV, (u₀.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := fun r hr =>
    (o₀.vcs r hr).trans (hv0 r hr)
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  obtain hin : ∀ p ∈ saved ++ regSlots, InRegions u₁.wr (u₁.gpr .x16 + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [e₁, o₁.wr]
    exact wr_frame hwr (by revert p; decide)
  refine Spill.save_ok (b := .x16) (l := saved ++ regSlots) fits.1 hin ?_
  generalize hm₂ : Spill.saveMem u₁.mem (u₁.gpr .x16) u₁.gpr (saved ++ regSlots) = m₂
  obtain fr₂ : Frame [⟨fb s, frameBytes⟩] s.mem m₂ := by
    rw [← hm₂, e₁, o₁.mem, hm]
    exact Spill.saveMem_frame_base (fun p hp' => by revert p; decide) (by decide) _ _ _
  obtain sv₂ : Spill.Saved (fb s) s.gpr (saved ++ regSlots) m₂ := by
    rw [← hm₂, e₁]
    intro p hp'
    rw [Spill.saveMem_saved fits _ _ _ p hp']
    have : p.1 ≠ .x16 := by revert p; decide
    obtain h10 : p.1 ≠ .x10 := by revert p; decide
    rw [o₁.get p.1 (by simpa using this), hg _ h10]
  obtain gs : ∀ r, r ≠ .x16 → r ≠ .x10 → u₁.gpr r = s.gpr r := fun r h h' => by
    rw [o₁.gpr r (by simpa using h), hg r h']
  refine wp_mov fun u₃ o₃ e₃ => ?_
  obtain sp₃ : u₃.sp = fb s := by rw [o₃.sp]; show u₁.sp = _; rw [o₁.sp, hsp]
  obtain rd₃ : u₃.rd = s.rd := by rw [o₃.rd]; show u₁.rd = _; rw [o₁.rd, hrd]
  obtain wr₃ : u₃.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₃.wr]; show u₁.wr = _; rw [o₁.wr, hwr]
  obtain x16₃ : u₃.gpr .x16 = fb s := by rw [o₃.get .x16]; exact e₁
  obtain aj : ∀ j, u₃.sp + BitVec.ofNat 64 (frameBytes + 8 * j) = stackArgAddr s j := fun j => by
    rw [sp₃, stackArgAddr_fb]
  obtain rj : ∀ j, j < 8 → InRegions (u₃.rd ++ u₃.wr) (stackArgAddr s j) 8 := fun j hj => by
    rw [rd₃]; exact arg_in hp (Covers.left (Covers.refl _)) hj
  -- `salt_len`.
  refine wp_ldrSp (by decide) (by rw [aj]; exact rj 0 (by decide)) fun a₁ oa₁ ea₁ => ?_
  rw [aj, o₃.mem, show ({ u₁ with mem := m₂ } : State).mem = m₂ from rfl, arg_frame hp fr₂ (by decide)] at ea₁
  refine wp_strx (by decide) (by rw [oa₁.get .x16, x16₃])
    (by rw [oa₁.wr, wr₃]; exact in_frame s _ (by decide)) fun a₂ ma₂ => ?_
  obtain fra₂ : Frame [⟨fb s, frameBytes⟩] s.mem a₂.mem := by
    rw [ma₂.mem, oa₁.mem, o₃.mem]
    exact fr₂.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain spa : a₂.sp = u₃.sp := by rw [ma₂.sp, oa₁.sp]
  obtain rda : a₂.rd = u₃.rd := by rw [ma₂.rd, oa₁.rd]
  obtain wra : a₂.wr = u₃.wr := by rw [ma₂.wr, oa₁.wr]
  obtain x16a : a₂.gpr .x16 = fb s := by rw [ma₂.gpr, oa₁.get .x16, x16₃]
  -- `any_salt_len`.
  refine wp_ldrSp (by decide) (by rw [spa, rda, wra, aj]; exact rj 1 (by decide)) fun u₄ o₄ e₄ => ?_
  rw [spa, aj, arg_frame hp fra₂ (by decide)] at e₄
  refine wp_movw fun u₄' o₄' e₄' => ?_
  rw [e₄] at e₄'
  refine wp_strx (by decide) (by rw [o₄'.get .x16, o₄.get .x16, x16a])
    (by rw [o₄'.wr, o₄.wr, wra, wr₃]; exact in_frame s _ (by decide)) fun u₅ m₅ => ?_
  obtain fr₅ : Frame [⟨fb s, frameBytes⟩] s.mem u₅.mem := by
    rw [m₅.mem, o₄'.mem, o₄.mem]
    exact fra₂.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain sp₅ : u₅.sp = u₃.sp := by rw [m₅.sp, o₄'.sp, o₄.sp, spa]
  obtain rd₅ : u₅.rd = u₃.rd := by rw [m₅.rd, o₄'.rd, o₄.rd, rda]
  obtain wr₅ : u₅.wr = u₃.wr := by rw [m₅.wr, o₄'.wr, o₄.wr, wra]
  -- `scratch` and `scratch_len`.
  refine wp_ldrSp (by decide) (by rw [sp₅, rd₅, wr₅, aj]; exact rj 2 (by decide)) fun u₁₀ o₁₀ e₁₀ => ?_
  rw [sp₅, aj, arg_frame hp fr₅ (by decide)] at e₁₀
  refine wp_ldrSp (by decide) (by rw [o₁₀.sp, o₁₀.rd, o₁₀.wr, sp₅, rd₅, wr₅, aj]; exact rj 3 (by decide))
    fun u₁₁ o₁₁ e₁₁ => ?_
  rw [o₁₀.sp, sp₅, aj, o₁₀.mem, arg_frame hp fr₅ (by decide)] at e₁₁
  obtain x16₁₁ : u₁₁.gpr .x16 = fb s := by
    rw [o₁₁.get .x16, o₁₀.get .x16, m₅.gpr, o₄'.get .x16, o₄.get .x16, x16a]
  refine wp_strx (by decide) (by rw [x16₁₁]) (by rw [o₁₁.wr, o₁₀.wr, wr₅, wr₃]; exact in_frame s _ (by decide))
    fun w₁ n₁ => ?_
  obtain fw₁ : Frame [⟨fb s, frameBytes⟩] s.mem w₁.mem := by
    rw [n₁.mem, o₁₁.mem, o₁₀.mem]
    exact fr₅.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain sp₁ : w₁.sp = u₃.sp := by rw [n₁.sp, o₁₁.sp, o₁₀.sp, sp₅]
  obtain rd₁ : w₁.rd = u₃.rd := by rw [n₁.rd, o₁₁.rd, o₁₀.rd, rd₅]
  obtain wr₁ : w₁.wr = u₃.wr := by rw [n₁.wr, o₁₁.wr, o₁₀.wr, wr₅]
  -- `pre` and `pre_len`.
  refine wp_ldrSp (by decide) (by rw [sp₁, rd₁, wr₁, aj]; exact rj 4 (by decide)) fun w₂ p₂ f₂ => ?_
  rw [sp₁, aj, arg_frame hp fw₁ (by decide)] at f₂
  obtain x16₂ : w₂.gpr .x16 = fb s := by rw [p₂.get .x16, n₁.gpr, x16₁₁]
  refine wp_strx (by decide) (by rw [x16₂]) (by rw [p₂.wr, wr₁, wr₃]; exact in_frame s _ (by decide))
    fun w₃ n₃ => ?_
  obtain fw₃ : Frame [⟨fb s, frameBytes⟩] s.mem w₃.mem := by
    rw [n₃.mem, p₂.mem]
    exact fw₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain r₅ : InRegions (w₃.rd ++ w₃.wr) (w₃.sp + BitVec.ofNat 64 (frameBytes + 8 * 5)) 8 := by
    rw [n₃.sp, p₂.sp, n₃.rd, p₂.rd, n₃.wr, p₂.wr, sp₁, rd₁, wr₁, aj]; exact rj 5 (by decide)
  refine wp_ldrSp (by decide) r₅ fun w₄ p₄ f₄ => ?_
  rw [n₃.sp, p₂.sp, sp₁, aj, arg_frame hp fw₃ (by decide)] at f₄
  refine wp_strx (by decide) (by rw [p₄.get .x16, n₃.gpr, x16₂])
    (by rw [p₄.wr, n₃.wr, p₂.wr, wr₁, wr₃]; exact in_frame s _ (by decide)) fun u₁₂ m₁₂ => ?_
  obtain fr₁₂ : Frame [⟨fb s, frameBytes⟩] s.mem u₁₂.mem := by
    rw [m₁₂.mem, p₄.mem]
    exact fw₃.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  -- The table's word 5, its index.
  obtain x10₁₂ : u₁₂.gpr .x10 = stackArg s 6 := by
    rw [m₁₂.gpr, p₄.get .x10, n₃.gpr, p₂.get .x10, n₁.gpr, o₁₁.get .x10, o₁₀.get .x10, m₅.gpr, o₄'.get .x10,
      o₄.get .x10, ma₂.gpr, oa₁.get .x10, o₃.get .x10]
    show u₁.gpr .x10 = _
    rw [o₁.get .x10, e₀]; rfl
  obtain rd₁₂ : u₁₂.rd = s.rd := by rw [m₁₂.rd, p₄.rd, n₃.rd, p₂.rd, rd₁, rd₃]
  obtain rtH : InRegions (u₁₂.rd ++ u₁₂.wr) (stackArg s 6 + BitVec.ofNat 64 40) 8 := by
    rw [rd₁₂]
    refine Covers.left (Covers.trans (Covers.of_mem fun x hx => by
      rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _ ⟨tHR s, List.mem_singleton_self _, ?_⟩
    exact Offset.contains_base _ (by decide) (by omega_using [])
  refine wp_ldrx (by decide) (by rw [x10₁₂]) rtH fun y₂ q₂ g₂ => ?_
  obtain x27b : y₂.gpr .x27 = s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 := by
    rw [g₂, fr₁₂.readW (r := ⟨stackArg s 6 + BitVec.ofNat 64 40, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ((hp.ktH.sub_left (frame_sub0 K s)).sub_right
          (Offset.sub_base _ (by decide))).symm) (by decide)]
  refine wp_addImm (by decide) fun u₁₃ o₁₃ e₁₃ => wp_addImm (by decide) fun u₁₄ o₁₄ e₁₄ => ?_
  obtain hm₁₂ : u₁₂.mem = ((((m₂.writeW (fb s + BitVec.ofNat 64 sSaltLen) (stackArg s 0)).writeW
      (fb s + BitVec.ofNat 64 sAny) (anyV s)).writeW
      (fb s + BitVec.ofNat 64 sScrLen) (stackArg s 3)).writeW (fb s + BitVec.ofNat 64 sPre) (stackArg s 4)).writeW
      (fb s + BitVec.ofNat 64 sPreLen) (stackArg s 5) := by
    rw [m₁₂.mem, p₄.mem, f₄, n₃.mem, p₂.mem, f₂, n₁.mem, o₁₁.mem, o₁₀.mem, m₅.mem, o₄'.mem, o₄.mem, ma₂.mem,
      oa₁.mem, o₃.mem, e₁₁, e₄', ea₁]
  obtain W5 : Frame [⟨fb s + BitVec.ofNat 64 sSaltLen, 8⟩, ⟨fb s + BitVec.ofNat 64 sAny, 8⟩,
      ⟨fb s + BitVec.ofNat 64 sScrLen, 8⟩, ⟨fb s + BitVec.ofNat 64 sPre, 8⟩,
      ⟨fb s + BitVec.ofNat 64 sPreLen, 8⟩] m₂ u₁₂.mem := by
    rw [hm₁₂]
    exact (((((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)
  obtain sv₁₂ : Spill.Saved (fb s) s.gpr (saved ++ regSlots) u₁₂.mem := sv₂.frame W5 fun p hp' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by revert p; decide) (by revert p; decide) (by decide)
  obtain sp₁₄ : u₁₄.sp = fb s := by rw [o₁₄.sp, o₁₃.sp, q₂.sp, m₁₂.sp, p₄.sp, n₃.sp, p₂.sp, sp₁, sp₃]
  obtain rd₁₄ : u₁₄.rd = s.rd := by rw [o₁₄.rd, o₁₃.rd, q₂.rd, rd₁₂]
  obtain wr₁₄ : u₁₄.wr = ⟨fb s, frameBytes⟩ :: s.wr := by
    rw [o₁₄.wr, o₁₃.wr, q₂.wr, m₁₂.wr, p₄.wr, n₃.wr, p₂.wr, wr₁, wr₃]
  obtain mem₁₄ : u₁₄.mem = u₁₂.mem := by rw [o₁₄.mem, o₁₃.mem, q₂.mem]
  obtain K₁₄ : Keep [.x9, .x10, .x16, .x19, .x20, .x21, .x23, .x27] { u₁ with mem := m₂ } u₁₄ :=
    (o₃.keep.trans (oa₁.keep.trans (ma₂.keep.trans (o₄.keep.trans (o₄'.keep.trans (m₅.keep.trans
      (o₁₀.keep.trans (o₁₁.keep.trans (n₁.keep.trans (p₂.keep.trans (n₃.keep.trans (p₄.keep.trans
      (m₁₂.keep.trans (q₂.keep.trans (o₁₃.keep.trans o₁₄.keep))))))))))))))).mono
  obtain x0₁₄ : u₁₄.gpr .x0 = s.gpr .x0 := by
    rw [K₁₄.gpr .x0 (by decide)]; exact gs .x0 (by decide) (by decide)
  have hk1 := hp.k1
  obtain rn : InRegions (u₁₄.rd ++ u₁₄.wr) (s.gpr .x0) 1 := by
    rw [rd₁₄, wr₁₄]
    refine Covers.left (Covers.trans (Covers.of_mem fun x hx => by
      rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _ ⟨nR s, List.mem_singleton_self _, ?_⟩
    have := Offset.contains_base (s.gpr .x0) (d := 0) (n := 1) (k := (s.gpr .x1).toNat) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  refine wp_ldrb (by decide) (by rw [x0₁₄, BitVec.add_zero]) rn fun u₁₆ o₁₆ e₁₆ => wp_nil ?_
  obtain hn₀ : u₁₄.mem (s.gpr .x0) = s.mem (s.gpr .x0) := by
    rw [mem₁₄]
    refine fr₁₂ _ fun r hr hc => ?_
    rw [List.mem_singleton.mp hr] at hc
    have := Offset.contains_base (s.gpr .x0) (d := 0) (n := 1) (k := (s.gpr .x1).toNat) (by omega_arith) (by omega_arith)
    rw [BitVec.add_zero] at this
    exact hp.kn _ (frame_sub0 K s _ hc) this
  obtain K : Keep [.x9, .x10, .x16, .x19, .x20, .x21, .x23, .x27] { u₁ with mem := m₂ } u₁₆ :=
    (K₁₄.trans o₁₆.keep).mono
  obtain mem₁₆ : u₁₆.mem = u₁₂.mem := by rw [o₁₆.mem, mem₁₄]
  obtain x20 : u₁₂.gpr .x20 = stackArg s 2 := by
    rw [m₁₂.gpr, p₄.get .x20, n₃.gpr, p₂.get .x20, n₁.gpr, o₁₁.get .x20, e₁₀]
  refine ⟨?sp, ?rd, ?wr, ?g, ?x10, ?x19, ?x20, ?x21, ?x27, ?x23, ?v, ?mem, ?fr⟩
  case sp => rw [o₁₆.sp, sp₁₄]
  case rd => rw [o₁₆.rd, rd₁₄]
  case wr => rw [o₁₆.wr, wr₁₄]
  case g =>
    intro r hr
    rw [K.gpr r hr]
    exact gs r (fun h => hr (by rw [h]; decide)) (fun h => hr (by rw [h]; decide))
  case x10 => rw [e₁₆, hn₀]
  case x19 => rw [o₁₆.get .x19, o₁₄.get .x19, e₁₃, q₂.get .x20, x20]
  case x20 => rw [o₁₆.get .x20, o₁₄.get .x20, o₁₃.get .x20, q₂.get .x20, x20]
  case x21 => rw [o₁₆.get .x21, e₁₄, o₁₃.get .x20, q₂.get .x20, x20]
  case x27 => rw [o₁₆.get .x27, o₁₄.get .x27, o₁₃.get .x27, x27b]
  case x23 =>
    rw [o₁₆.get .x23, o₁₄.get .x23, o₁₃.get .x23, q₂.get .x23, m₁₂.gpr, p₄.get .x23, n₃.gpr, p₂.get .x23,
      n₁.gpr, o₁₁.get .x23, o₁₀.get .x23, m₅.gpr, o₄'.get .x23, o₄.get .x23, ma₂.gpr, oa₁.get .x23, e₃]
    exact gs .x1 (by decide) (by decide)
  case v =>
    intro r hr
    rw [K.vcs r hr]
    show (u₁.v r).extractLsb' 0 64 = _
    rw [o₁.vcs r hr, hv r hr]
  case mem => rw [mem₁₆]; exact fr₁₂
  case fr =>
    rw [mem₁₆]
    obtain r2 : ∀ {d : Nat}, d + 8 ≤ frameBytes → (d + 8 ≤ sPre ∨ sPreLen + 8 ≤ d) →
        u₁₂.mem.readW (fb s + BitVec.ofNat 64 d) 64 = Mem.readW (((m₂.writeW (fb s + BitVec.ofNat 64 sSaltLen)
          (stackArg s 0)).writeW (fb s + BitVec.ofNat 64 sAny) (anyV s)).writeW (fb s + BitVec.ofNat 64 sScrLen)
          (stackArg s 3)) (fb s + BitVec.ofNat 64 d) 64 :=
      fun hd h => by
        rw [hm₁₂, Mem.readW_writeW_sep (Offset.sep _ (by unfold sPre sPreLen at *; omega_arith)
          (by unfold frameBytes at hd; omega_arith) (by decide)) (by decide),
          Mem.readW_writeW_sep (Offset.sep _ (by unfold sPre sPreLen at *; omega_arith)
          (by unfold frameBytes at hd; omega_arith) (by decide)) (by decide)]
    refine ⟨sv₁₂.sub fun p hp => List.mem_append_left _ hp, sv₁₂.sub fun p hp => List.mem_append_right _ hp,
      ?_, by rw [r2 (by decide) (by decide), Mem.readW_writeW_self64], ?_, ?_, ?_⟩
    · rw [r2 (by decide) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide))
        (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    · rw [r2 (by decide) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide))
        (by decide), Mem.readW_writeW_self64]
    · rw [hm₁₂, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    · rw [hm₁₂, Mem.readW_writeW_self64]

end VG.Proof.RsaPss.AArch64.Vfy

end

end


/-!
# RSASSA-PSS verification on AArch64: the call of the public operation

`pubArgs_ok`: after `emBitsB` (`PreCall`), the call's stack arguments and
registers (`AtCall`); `call_ok`: the call writes RSAVP1 of the signature (or
zeros) to the start of the working space and keeps the frame and our
registers (`AfterCall`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil wp_movz wp_add wp_addImm wp_subImm)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov setWidth_ofNat16 PdChecked PdOk PubLay pdRd
  pubWr pdCall sa0)
open VG.Proof.RsaPss.AArch64 (off)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb fb_eq frame_sub frame_sub0 below_fb below_sub in_frame)

/-- The working space. -/
abbrev scr (s : State) : Addr := stackArg s 2

/-- The call's output, and its working space. -/
abbrev outR (s : State) : Region := ⟨scr s, (s.gpr .x1).toNat⟩
abbrev scR (s : State) : Region := ⟨off (scr s) oRsa, (stackArg s 3 - BitVec.ofNat 64 1024).toNat * 8⟩

theorem scr_toNat {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) :
    (stackArg s 3 - BitVec.ofNat 64 1024).toNat = (stackArg s 3).toNat - 1024 := by
  have := hp.hs
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (stackArg s 3).isLt
  omega_arith

theorem out_sub {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) : Region.Sub (outR s) (sR s) :=
  Region.sub_prefix (by have := hp.hs; have := hp.k2; omega_arith)

theorem sc_sub {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) : Region.Sub (scR s) (sR s) :=
  Offset.sub_base _ (by rw [scr_toNat hp]; have := hp.hs; unfold oRsa; omega_arith)

theorem a16_sub (K : Nat) (s : State) : Region.Sub ⟨fb s, 16⟩ (kR K s) := by
  have := frame_sub K s (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this

/-- After `emBitsB`, with `emBits`, `emLen` and `lo` in `x24`, `x25` and
`x26`. -/
structure PreCall (s : State) (eb el lo : Nat) (w : State) : Prop where
  sp : w.sp = fb s
  rd : w.rd = s.rd
  wr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x20 : w.gpr .x20 = scr s
  x23 : w.gpr .x23 = s.gpr .x1
  x24 : w.gpr .x24 = BitVec.ofNat 64 eb
  x25 : w.gpr .x25 = BitVec.ofNat 64 el
  x26 : w.gpr .x26 = BitVec.ofNat 64 lo
  x27 : w.gpr .x27 = s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64
  v : ∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem w.mem
  fr : Fr s w.mem

/-- At the call. -/
structure AtCall (s : State) (eb el lo : Nat) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x0 : t.gpr .x0 = scr s
  x1 : t.gpr .x1 = s.gpr .x1
  x2 : t.gpr .x2 = stackArg s 4
  x3 : t.gpr .x3 = stackArg s 5
  x4 : t.gpr .x4 = s.gpr .x2
  x5 : t.gpr .x5 = s.gpr .x3
  x6 : t.gpr .x6 = s.gpr .x6
  x7 : t.gpr .x7 = s.gpr .x1
  x20 : t.gpr .x20 = scr s
  x23 : t.gpr .x23 = s.gpr .x1
  x24 : t.gpr .x24 = BitVec.ofNat 64 eb
  x25 : t.gpr .x25 = BitVec.ofNat 64 el
  x26 : t.gpr .x26 = BitVec.ofNat 64 lo
  x27 : t.gpr .x27 = s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  a0 : stackArg t 0 = off (scr s) oRsa
  a1 : stackArg t 1 = stackArg s 3 - BitVec.ofNat 64 1024
  mem : Frame [⟨fb s, frameBytes⟩] s.mem t.mem
  fr : Fr s t.mem

theorem fr16 (s : State) : ∀ r ∈ [(⟨fb s, 16⟩ : Region)],
    (frA s).Disjoint r ∧ (frB s).Disjoint r ∧ (frC s).Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨Offset.disjoint_base _ (by decide) (by decide), Offset.disjoint_base _ (by decide) (by decide),
    Offset.disjoint_base _ (by decide) (by decide)⟩

theorem pubArgs_ok {s w : State} {eb el lo : Nat} (hm : PreCall s eb el lo w) :
    WP isa (.block pubArgsC) w (AtCall s eb el lo) := by
  unfold pubArgsC ld
  obtain rsl : ∀ {u : State} {d : Nat}, u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      d + 8 ≤ frameBytes → InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr hd => by
    rw [hsp, hrd, hwr]
    exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega_arith)))
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_add fun u₃ o₃ e₃ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  obtain O₃ : Only [.x16, .x9] w u₃ := (o₁.trans (o₂.trans o₃)).mono
  obtain x9₃ : u₃.gpr .x9 = off (scr s) oRsa := by
    rw [e₃, e₂, o₂.get .x20, o₁.get .x20, hm.x20, setWidth_ofNat16 (by decide)]
  refine wp_strx (a := fb s + BitVec.ofNat 64 0) (by decide) (by rw [o₃.get .x16, o₂.get .x16, e₁])
    (by rw [O₃.wr, hm.wr]; exact in_frame _ _ (by decide)) fun u₄ m₄ => ?_
  obtain sp₄ : u₄.sp = fb s := by rw [m₄.sp, O₃.sp, hm.sp]
  obtain rd₄ : u₄.rd = s.rd := by rw [m₄.rd, O₃.rd, hm.rd]
  obtain wr₄ : u₄.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₄.wr, O₃.wr, hm.wr]
  obtain f₄ : Frame [(⟨fb s, 16⟩ : Region)] w.mem u₄.mem := by
    rw [m₄.mem, O₃.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain frX : ∀ {m : Mem}, Frame [(⟨fb s, 16⟩ : Region)] w.mem m → Fr s m := fun h =>
    hm.fr.frame h (fun r hr => ((fr16 s) r hr).1) (fun r hr => ((fr16 s) r hr).2.1) (fun r hr => ((fr16 s) r hr).2.2)
  refine wp_ldrSp (by decide) (rsl sp₄ rd₄ wr₄ (by decide)) fun u₅ o₅ e₅ => ?_
  rw [sp₄, (frX f₄).scr] at e₅
  refine wp_subImm (by decide) fun u₆ o₆ e₆ => ?_
  obtain x16₆ : u₆.gpr .x16 = fb s := by rw [o₆.get .x16, o₅.get .x16, m₄.gpr, o₃.get .x16, o₂.get .x16, e₁]
  refine wp_strx (a := fb s + BitVec.ofNat 64 8) (by decide) (by rw [x16₆])
    (by rw [o₆.wr, o₅.wr, wr₄]; exact in_frame _ _ (by decide)) fun u₇ m₇ => ?_
  obtain hm₇ : u₇.mem = (w.mem.writeW (fb s + BitVec.ofNat 64 0) (off (scr s) oRsa)).writeW
      (fb s + BitVec.ofNat 64 8) (stackArg s 3 - BitVec.ofNat 64 1024) := by
    rw [m₇.mem, o₆.mem, o₅.mem, e₆, e₅, m₄.mem, O₃.mem, x9₃]
  obtain f₇ : Frame [(⟨fb s, 16⟩ : Region)] w.mem u₇.mem := by
    rw [hm₇]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain F₇ := frX f₇
  obtain sp₇ : u₇.sp = fb s := by rw [m₇.sp, o₆.sp, o₅.sp, sp₄]
  obtain rd₇ : u₇.rd = s.rd := by rw [m₇.rd, o₆.rd, o₅.rd, rd₄]
  obtain wr₇ : u₇.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₇.wr, o₆.wr, o₅.wr, wr₄]
  obtain K₇ : Keep [.x16, .x9] w u₇ := (O₃.keep.trans (m₄.keep.trans (o₅.keep.trans (o₆.keep.trans m₇.keep)))).mono
  refine wp_mov fun u₈ o₈ e₈ => wp_mov fun u₉ o₉ e₉ => ?_
  refine wp_ldrSp (by decide) (by rw [o₉.sp, o₈.sp, o₉.rd, o₈.rd, o₉.wr, o₈.wr]; exact rsl sp₇ rd₇ wr₇ (by decide))
    fun u₁₀ o₁₀ e₁₀ => ?_
  obtain r₁₀ : InRegions (u₁₀.rd ++ u₁₀.wr) (u₁₀.sp + BitVec.ofNat 64 sPreLen) 8 := by
    rw [o₁₀.sp, o₉.sp, o₈.sp, o₁₀.rd, o₉.rd, o₈.rd, o₁₀.wr, o₉.wr, o₈.wr]; exact rsl sp₇ rd₇ wr₇ (by decide)
  refine wp_ldrSp (by decide) r₁₀ fun u₁₁ o₁₁ e₁₁ => ?_
  obtain sp₁₁ : u₁₁.sp = fb s := by rw [o₁₁.sp, o₁₀.sp, o₉.sp, o₈.sp, sp₇]
  obtain rd₁₁ : u₁₁.rd = s.rd := by rw [o₁₁.rd, o₁₀.rd, o₉.rd, o₈.rd, rd₇]
  obtain wr₁₁ : u₁₁.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₁₁.wr, o₁₀.wr, o₉.wr, o₈.wr, wr₇]
  obtain mem₁₁ : u₁₁.mem = u₇.mem := by rw [o₁₁.mem, o₁₀.mem, o₉.mem, o₈.mem]
  refine wp_ldrSp (by decide) (rsl sp₁₁ rd₁₁ wr₁₁ (by decide)) fun u₁₂ o₁₂ e₁₂ => ?_
  refine wp_ldrSp (by decide) (by rw [o₁₂.sp, o₁₂.rd, o₁₂.wr]; exact rsl sp₁₁ rd₁₁ wr₁₁ (by decide))
    fun u₁₃ o₁₃ e₁₃ => ?_
  obtain r₁₃ : InRegions (u₁₃.rd ++ u₁₃.wr) (u₁₃.sp + BitVec.ofNat 64 sOut) 8 := by
    rw [o₁₃.sp, o₁₂.sp, o₁₃.rd, o₁₂.rd, o₁₃.wr, o₁₂.wr]; exact rsl sp₁₁ rd₁₁ wr₁₁ (by decide)
  refine wp_ldrSp (by decide) r₁₃ fun u₁₄ o₁₄ e₁₄ => wp_mov fun u₁₅ o₁₅ e₁₅ => wp_nil ?_
  obtain O : Only [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] u₇ u₁₅ :=
    (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))))))).mono
  obtain x23 : u₇.gpr .x23 = s.gpr .x1 := by rw [K₇.get .x23, hm.x23]
  rw [o₉.sp, o₈.sp, sp₇, o₉.mem, o₈.mem, F₇.pre] at e₁₀
  rw [o₁₀.sp, o₉.sp, o₈.sp, sp₇, o₁₀.mem, o₉.mem, o₈.mem, F₇.preLen] at e₁₁
  rw [sp₁₁, mem₁₁, F₇.rs (.x2, sE) (by simp [regSlots])] at e₁₂
  rw [o₁₂.sp, sp₁₁, o₁₂.mem, mem₁₁, F₇.rs (.x3, sEl) (by simp [regSlots])] at e₁₃
  rw [o₁₃.sp, o₁₂.sp, sp₁₁, o₁₃.mem, o₁₂.mem, mem₁₁, F₇.rs (.x6, sOut) (by simp [regSlots])] at e₁₄
  have mem₁₅ : u₁₅.mem = u₇.mem := O.mem
  exact {
    sp := by rw [o₁₅.sp, o₁₄.sp, o₁₃.sp, o₁₂.sp, sp₁₁]
    rd := by rw [o₁₅.rd, o₁₄.rd, o₁₃.rd, o₁₂.rd, rd₁₁]
    wr := by rw [o₁₅.wr, o₁₄.wr, o₁₃.wr, o₁₂.wr, wr₁₁]
    x0 := by
      rw [o₁₅.get .x0, o₁₄.get .x0, o₁₃.get .x0, o₁₂.get .x0, o₁₁.get .x0, o₁₀.get .x0, o₉.get .x0, e₈,
        K₇.get .x20, hm.x20]
    x1 := by rw [o₁₅.get .x1, o₁₄.get .x1, o₁₃.get .x1, o₁₂.get .x1, o₁₁.get .x1, o₁₀.get .x1, e₉, o₈.get .x23, x23]
    x2 := by rw [o₁₅.get .x2, o₁₄.get .x2, o₁₃.get .x2, o₁₂.get .x2, o₁₁.get .x2, e₁₀]
    x3 := by rw [o₁₅.get .x3, o₁₄.get .x3, o₁₃.get .x3, o₁₂.get .x3, e₁₁]
    x4 := by rw [o₁₅.get .x4, o₁₄.get .x4, o₁₃.get .x4, e₁₂]
    x5 := by rw [o₁₅.get .x5, o₁₄.get .x5, e₁₃]
    x6 := by rw [o₁₅.get .x6, e₁₄]
    x7 := by
      rw [e₁₅, o₁₄.get .x23, o₁₃.get .x23, o₁₂.get .x23, o₁₁.get .x23, o₁₀.get .x23, o₉.get .x23, o₈.get .x23, x23]
    x20 := by rw [O.get .x20, K₇.get .x20, hm.x20]
    x23 := by rw [O.get .x23, K₇.get .x23, hm.x23]
    x24 := by rw [O.get .x24, K₇.get .x24, hm.x24]
    x25 := by rw [O.get .x25, K₇.get .x25, hm.x25]
    x26 := by rw [O.get .x26, K₇.get .x26, hm.x26]
    x27 := by rw [O.get .x27, K₇.get .x27, hm.x27]
    v := fun r hr => by rw [O.vcs r hr, K₇.vcs r hr, hm.v r hr]
    a0 := by
      show u₁₅.mem.readW (stackArgAddr u₁₅ 0) 64 = _
      rw [sa0, mem₁₅, o₁₅.sp, o₁₄.sp, o₁₃.sp, o₁₂.sp, sp₁₁, hm₇]
      conv => lhs; arg 2; rw [← BitVec.add_zero (fb s)]
      rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    a1 := by
      show u₁₅.mem.readW (stackArgAddr u₁₅ 1) 64 = _
      rw [stackArgAddr, mem₁₅, o₁₅.sp, o₁₄.sp, o₁₃.sp, o₁₂.sp, sp₁₁, hm₇]
      exact Mem.readW_writeW_self64 _ _ _
    mem := by
      rw [mem₁₅]
      exact hm.mem.trans (f₇.sub fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ⟨⟨fb s, frameBytes⟩, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
    fr := by rw [mem₁₅]; exact F₇ }

/-! ## The call -/

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat)

/-- `pre` holds the modulus' precomputed values. -/
def Cons (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat)

/-- After the call. -/
structure AfterCall (K : Nat) (s : State) (eb el lo : Nat) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x20 : t.gpr .x20 = scr s
  x23 : t.gpr .x23 = s.gpr .x1
  x24 : t.gpr .x24 = BitVec.ofNat 64 eb
  x25 : t.gpr .x25 = BitVec.ofNat 64 el
  x26 : t.gpr .x26 = BitVec.ofNat 64 lo
  x27 : t.gpr .x27 = s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [kR K s, sR s] s.mem t.mem
  fr : Fr s t.mem
  res : Cons s → Spec.Rsa.written t.mem (scr s) (s.gpr .x1).toNat ((t.gpr .x0).setWidth 32) (pubOut s)

theorem pdOk_of (c : PdChecked) {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreV tsH tsG K s) (hcK : c.stack ≤ K) {eb el lo : Nat}
    (ha : AtCall s eb el lo t) : PdOk c.stack t := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hfb := fb_toNat hp
  obtain hkb := kb_toNat hp
  have hcl := c.le
  have hpos := c.pos
  have hws : (scr s).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 := hp.ws
  obtain hsc := scr_toNat hp
  have hhs := hp.hs
  obtain hK : Region.Sub ⟨fb s - BitVec.ofNat 64 c.stack, c.stack⟩ (kR K s) := fun a h =>
    (Offset.sub_below (fb s) (a := c.stack) (b := K) (n := c.stack) (m := K) hcK (by omega_arith) a h) |>
      fun h' => by
        obtain e : fb s - BitVec.ofNat 64 K = kb K s := by rw [fb_eq K, BitVec.add_sub_cancel]
        rw [e] at h'
        exact Region.sub_prefix (by unfold stk; omega_arith) a h'
  obtain hsg : (⟨s.gpr .x6, (s.gpr .x1).toNat⟩ : Region) = sgR s := by rw [sgR, hp.sgl]
  obtain s16 := a16_sub K s
  obtain hSem := out_sub hp
  obtain hSsc := sc_sub hp
  obtain hwem : (scr s).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 := by omega_arith
  obtain hwsc : (off (scr s) oRsa).toNat + (stackArg s 3 - BitVec.ofNat 64 1024).toNat * 8 ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; rw [hsc]; unfold oRsa at *; omega_arith
  refine ⟨?hl, ?hrd, ?hwr, ?hk, ?h3, ?h7, ?he1, ?he2, ?hs⟩
  case hl =>
    rw [ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, ha.sp, ha.a0, ha.a1]
    obtain hsgS : (⟨s.gpr .x6, (s.gpr .x1).toNat⟩ : Region).Disjoint (sR s) := by rw [hsg]; exact hp.sgs
    obtain hsgK : (kR K s).Disjoint ⟨s.gpr .x6, (s.gpr .x1).toNat⟩ := by rw [hsg]; exact hp.ksg
    exact {
      sp1 := by unfold stk at *; omega_arith
      sp2 := by omega_arith
      on := hp.sP.sub_left hSem
      oe := (hp.es.sub_right hSem).symm
      oi := (hsgS.sub_right hSem).symm
      os := by
        obtain h := Offset.disjoint (scr s) (d := 0) (n := (s.gpr .x1).toNat) (e := oRsa)
          (k := (stackArg s 3 - BitVec.ofNat 64 1024).toNat * 8) (Or.inl (by unfold oRsa; omega_arith))
          (by omega_arith) (by rw [hsc]; unfold oRsa; omega_arith)
        rwa [BitVec.add_zero] at h
      oa := ((hp.ks.sub_left s16).sub_right hSem).symm
      ns := (hp.sP.sub_left hSsc).symm
      es := hp.es.sub_right hSsc
      is := hsgS.sub_right hSsc
      sa := ((hp.ks.sub_left s16).symm.sub_left hSsc)
      ko := (hp.ks.sub_left hK).sub_right hSem
      kn := hp.kP.sub_left hK
      ke := hp.ke.sub_left hK
      ki := hsgK.sub_left hK
      ks := (hp.ks.sub_left hK).sub_right hSsc
      ka := (Offset.base_disjoint_below (fb s) (n := c.stack) (k := 16) (by omega_arith)).symm
      wo := hwem
      wn := hp.wP
      we := hp.we
      wi := by have := hp.wsg; rw [hp.sgl] at this; exact this
      ws := hwsc }
  case hrd =>
    simp only [pdRd]
    rw [ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, ha.sp, ha.rd, ha.wr, hsg]
    obtain hm : ∀ r ∈ [nR s, eR s, dgR s, sgR s, pR s, tHR s, tGR s, aR s], Covers [r] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr)) :=
      fun r hr => Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
        hp.hrd)
    refine Covers.cons (hm (pR s) (by simp)) (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp))
      (Covers.right (Covers.one ?_))))
    simpa using in_frame s s.wr (d := 0) (n := 16) (by decide)
  case hwr =>
    simp only [pubWr]
    rw [ha.x0, ha.x1, ha.a0, ha.a1, ha.wr]
    obtain hc := Offset.contains_base (scr s) (d := 0) (n := (s.gpr .x1).toNat) (k := (stackArg s 3).toNat * 8)
      (by have := hp.hs; have := hp.k2; omega_arith) (by decide)
    rw [BitVec.add_zero] at hc
    exact Covers.cons (Covers.one ⟨sR s, List.mem_cons_of_mem _ hp.hws, hc⟩)
      (Covers.one ⟨sR s, List.mem_cons_of_mem _ hp.hws,
        Offset.contains_base _ (by rw [hsc]; unfold oRsa; omega_arith) (by unfold oRsa; omega_arith)⟩)
  case hk => rw [ha.x1]; exact ⟨hk1, hk2⟩
  case h3 => rw [ha.x3, ha.x1]; exact hp.hl
  case h7 => rw [ha.x7, ha.x1]
  case he1 => rw [ha.x5]; exact hp.e1
  case he2 => rw [ha.x5, ha.x1]; exact hp.e2
  case hs => rw [ha.a1, ha.x1, hsc]; unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; omega_arith

theorem call_ok (c : PdChecked) {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreV tsH tsG K s) (hcK : c.stack ≤ K)
    {eb el lo : Nat} (ha : AtCall s eb el lo t) :
    WP isa (.call c.name c.code) t (AfterCall K s eb el lo) := by
  obtain hfb := fb_toNat hp
  obtain hkb := kb_toNat hp
  have hcl := c.le
  have hd := c.depth
  refine pdCall c (pdOk_of c hp hcK ha) fun s' hrd' hwr' hsp' hf hpres hvs hpost => ?_
  simp only [pubWr] at hf
  rw [ha.x0, ha.x1, ha.a0, ha.a1, ha.sp] at hf
  obtain hbs : Region.Sub (below (fb s) (16 * c.code.aarch64Depth)) (kR K s) := fun a h =>
    below_sub K s a (Offset.sub_below (fb s) (a := 16 * c.code.aarch64Depth) (b := K)
      (n := 16 * c.code.aarch64Depth) (m := K) (by omega_arith) (by omega_arith) a h)
  obtain hf' : Frame [kR K s, sR s] t.mem s'.mem := hf.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), out_sub hp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), sc_sub hp⟩
    · exact ⟨_, List.mem_cons_self .., hbs⟩
  obtain hfr0 : Frame [kR K s, sR s] s.mem t.mem := ha.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub0 K s⟩
  obtain hbt : ∀ {p : Addr} {len : Nat}, (kR K s).Disjoint ⟨p, len⟩ → (sR s).Disjoint ⟨p, len⟩ →
      len ≤ 2 ^ 64 → ∀ i < len, t.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) :=
    fun hk hs hl i hi => hfr0.bytes (R := ⟨_, _⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hk.symm
      · exact hs.symm) hl hi
  obtain hbytes : ∀ {p : Addr} {len : Nat}, (kR K s).Disjoint ⟨p, len⟩ → (sR s).Disjoint ⟨p, len⟩ →
      len ≤ 2 ^ 64 → Spec.Rsa.bytesAt t.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk hs hl => by
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hbt hk hs hl i (List.mem_range.mp hi)
  obtain hsg : (⟨s.gpr .x6, (s.gpr .x1).toNat⟩ : Region) = sgR s := by rw [sgR, hp.sgl]
  obtain hwords : Spec.Rsa.wordsAt t.mem (stackArg s 4) (stackArg s 5).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat := by
    simp only [Spec.Rsa.wordsAt]
    refine List.map_congr_left fun i hi => ?_
    obtain hi' := List.mem_range.mp hi
    exact hfr0.readW (r := pR s) (Offset.contains_base _ (by omega_arith) (by have := hp.wP; omega_arith)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.kP.symm
      · exact hp.sP.symm) (by decide)
  obtain hA : ∀ {d n : Nat}, d + n ≤ frameBytes → ∀ r ∈ [outR s, scR s] ++ [below (fb s) (16 * c.code.aarch64Depth)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := fun hdn r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.ks.sub_left (frame_sub K s hdn)).sub_right (out_sub hp)
    · exact (hp.ks.sub_left (frame_sub K s hdn)).sub_right (sc_sub hp)
    · exact Offset.disjoint_below _ (by unfold frameBytes at hdn; omega_arith)
  exact {
    sp := hsp'.trans ha.sp
    rd := hrd'.trans ha.rd
    wr := hwr'.trans ha.wr
    x20 := (hpres .x20 (by decide) (by decide)).trans ha.x20
    x23 := (hpres .x23 (by decide) (by decide)).trans ha.x23
    x24 := (hpres .x24 (by decide) (by decide)).trans ha.x24
    x25 := (hpres .x25 (by decide) (by decide)).trans ha.x25
    x26 := (hpres .x26 (by decide) (by decide)).trans ha.x26
    x27 := (hpres .x27 (by decide) (by decide)).trans ha.x27
    v := fun r hr => (hvs r hr).trans (ha.v r hr)
    mem := hfr0.trans hf'
    fr := ha.fr.frame hf (hA (by decide)) (hA (by decide)) (hA (by decide))
    res := fun hc => by
      have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, ha.x1]) (by rw [ha.x2, ha.x3, hwords]; exact hc)
      rw [ha.x0, ha.x1, ha.x4, ha.x5, ha.x6, hbytes hp.ke hp.es.symm (by have := hp.we; omega_arith),
        hbytes (len := (s.gpr .x1).toNat) (by rw [hsg]; exact hp.ksg) (by rw [hsg]; exact hp.sgs.symm)
          (by have := hp.wsg; rw [hp.sgl] at this; omega_arith)] at this
      exact this }

end VG.Proof.RsaPss.AArch64.Vfy

end

end


/-!
# RSASSA-PSS verification on AArch64: the result, by cases

`verifyOut Hs Gs s`: what the contract asks of a call from `s`. It is `false`
if the modulus' first byte is zero (`verifyOut_zero`), and otherwise that
RSAVP1's result, or zeros, starts with `lo` zero bytes and ends with a
consistent encoding of `emBits = 8 (k - 1) + log₂ n₀` bits
(`verifyOut_enc`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64 (ebV)
open VG.Proof.RsaPss.AArch64.Sgn (bytesAt_cons fb)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- In the frame: the slots and the callee-saved registers' values. -/
structure Mid (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : Fr s t.mem

/-- RSAVP1's result, or zeros. -/
abbrev pubX (s : State) : List Byte := (pubOut s).getD (Spec.RsaPss.zeros (s.gpr .x1).toNat)

/-- The salt length `verify` expects. -/
abbrev sLenV (s : State) : Option Nat := if anyV s = 0 then some (stackArg s 0).toNat else none

/-- `emBits`, `emLen` and `lo` of a call from `s`. -/
abbrev ebS (s : State) : Nat := ebV (s.gpr .x1).toNat (s.mem (s.gpr .x0)).toNat
abbrev elS (s : State) : Nat := Spec.RsaPss.emLength (ebS s)
abbrev loS (s : State) : Nat := (s.gpr .x1).toNat - elS s

theorem pubX_length (s : State) : (pubX s).length = (s.gpr .x1).toNat := by
  unfold pubX
  cases h : pubOut s with
  | none => simp [Spec.RsaPss.zeros]
  | some y => rw [Option.getD_some, RsaPss.publicOpChecked_length' h, bytesAt_length]

variable (Hs Gs : Spec.Mgf1.Hash)

/-- The result `verifyPrecomputedMdTableContract.post` asks for, with the hash
function `Hs` and MGF1's `Gs`. -/
def verifyOut (s : State) : Bool :=
  Spec.RsaPss.verify Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x4) Hs.len)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat)
    (Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32))

theorem anyV_eq (s : State) : anyV s = 0 ↔ (stackArg s 1).setWidth 32 = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [anyV, BitVec.toNat_setWidth] at this ⊢
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
    rw [show (0 : BitVec 32).toNat = 0 from rfl]
    omega_using [this]
  · intro h; unfold anyV; rw [h]; rfl

theorem expected_eq (s : State) :
    Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32) = sLenV s := by
  unfold Spec.RsaPss.expectedSaltLen sLenV
  by_cases h : anyV s = 0
  · rw [ite_eq_left h, ite_eq_left ((anyV_eq s).mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun e => h ((anyV_eq s).mpr e))]

theorem verifyOut_zero {s : State} (hk : 1 ≤ (s.gpr .x1).toNat) (h0 : s.mem (s.gpr .x0) = 0) :
    verifyOut Hs Gs s = false := by
  unfold verifyOut
  rw [bytesAt_cons _ _ hk, h0]
  exact RsaPss.verify_zero₂ Gs Hs ..

section
variable {s : State} (hk1 : 64 ≤ (s.gpr .x1).toNat) (hk2 : (s.gpr .x1).toNat ≤ 1024)
  (h0 : s.mem (s.gpr .x0) ≠ 0)
include hk1 hk2 h0

theorem eb_bounds : 1 ≤ ebS s ∧ ebS s ≤ Proof.RsaPss.maxEmBits ∧ loS s + elS s = (s.gpr .x1).toNat ∧ loS s ≤ 1 := by
  have h0' : (s.mem (s.gpr .x0)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hl8 := RsaPss.log2_lt8 (s.mem (s.gpr .x0))
  unfold loS elS ebS Spec.RsaPss.emLength ebV Proof.RsaPss.maxEmBits
  omega_using [hk1, hk2, hl8]

omit hk2 in
/-- `emBits`, from the modulus' length and first byte. -/
theorem emBits_of :
    Spec.RsaPss.bitLength (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)) - 1 = ebS s := by
  rw [bytesAt_cons _ _ (by omega_using [hk1]), RsaPss.emBits_eq _ h0, bytesAt_length]
  rfl

/-- Verifying: `lo` zero bytes, then a consistent encoding. -/
theorem verifyOut_enc :
    verifyOut Hs Gs s = ((pubX s).take (loS s) == Spec.RsaPss.zeros (loS s) &&
      Spec.RsaPss.verifyEncoding Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .x4) Hs.len) ((pubX s).drop (loS s)) (ebS s)
        (sLenV s)) := by
  obtain ⟨hb1, -, hlok, -⟩ := eb_bounds hk1 hk2 h0
  obtain hel : 1 ≤ elS s := by unfold elS Spec.RsaPss.emLength; omega_using [hb1]
  unfold verifyOut pubX pubOut
  rw [expected_eq, RsaPss.verify_encode₂ Hs Gs (emBits_of hk1 h0) (by rw [bytesAt_length, bytesAt_length])
    (by rw [bytesAt_length]; unfold elS at hlok hel; omega_using [hk1, hel]), bytesAt_length]

end

/-- `lo ≤ 1` zero bytes: none, or the first byte zero. -/
theorem take_zeros {x : List Byte} {lo : Nat} (hlo : lo ≤ 1) (hx : 1 ≤ x.length) :
    (x.take lo == Spec.RsaPss.zeros lo) = (lo == 0 || x.getD 0 0 == 0) := by
  rcases (by omega_using [hlo] : lo = 0 ∨ lo = 1) with rfl | rfl
  · rfl
  · obtain ⟨b, x, rfl⟩ : ∃ b y, x = b :: y := by
      cases x with
      | nil => simp at hx
      | cons b y => exact ⟨b, y, rfl⟩
    simp [Spec.RsaPss.zeros]

end VG.Proof.RsaPss.AArch64.Vfy
