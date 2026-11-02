module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Comb
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.ScalarBase
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

/-!
# `vg_ed25519_scalar_base` on PPC64LE: its contract

As on RISC-V (`Proof/Ed25519/RISCV64/BaseContract.lean`): the precondition by register
(`BasePre`), with the comb's table, the static `combSym`, at `TBL`; the contract of the
internal function (`baseRV`), and what its proof gives (`BaseOk`, proven by
`ScalarBase.lean`'s `base_ok`), so that the functions that call it need not import the comb's
proofs; the table's facts under `abi.withConsts combConsts` (`tbl_of_consts`,
`rd_of_consts`), the precondition on entry to a call (`basePre_call`), and that a
contract by register without the table implies one under `abi.withConsts combConsts`
(`consts_implies`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)

/-- The region of the comb's tables at `T`. -/
abbrev TBL (T : Addr) : Region := ⟨T, 49152⟩

/-- The precondition, by register: `out` in `r3`, `scalar` in `r4`, `scratch` in `r5`. -/
structure BasePre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 32⟩, TBL (s.syms combSym)]
  wr : s.wr = [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r5, 8192⟩]
  out_ws : (⟨s.gpr .r3, 32⟩ : Region).Disjoint ⟨s.gpr .r5, 8192⟩
  sc_ws : (⟨s.gpr .r4, 32⟩ : Region).Disjoint ⟨s.gpr .r5, 8192⟩
  tfit : (s.syms combSym).toNat + 49152 ≤ 2 ^ 64
  words : ∀ q < 64 * 96, s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q
  tbl_ws : (TBL (s.syms combSym)).Disjoint ⟨s.gpr .r5, 8192⟩

/-- `vg_ed25519_scalar_base`'s contract by register, an internal function's: `BasePre`. -/
def baseRV : Contract isa where
  pre := BasePre
  post s s' := bytesAt s'.mem (s.gpr .r3) 32 = Spec.Ed25519.scalarBase (bytesAt s.mem (s.gpr .r4) 32)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp ∧
    s₁.syms combSym = s₂.syms combSym

/-- What the proof of `vg_ed25519_scalar_base` gives. -/
def BaseOk : Prop := ∀ s, baseRV.pre s → ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ baseRV.post s s'

theorem combWords_length : combWords.length = 64 * 96 := by simp [combWords]

theorem combWords_getD {q : Nat} (hq : q < 64 * 96) : combWords.getD q 0 = combWord q := by
  simp [combWords, hq]

/-- What `abi.withConsts [(combSym, ws)]` says of the comb's table, for words `ws` of `combWord`. -/
theorem tbl_of_consts' {st : Nat} {s : State} {ws : List (BitVec 64)} (hl : ws.length = 64 * 96)
    (hg : ∀ q < 64 * 96, ws.getD q 0 = combWord q) (h : ConstsOk [(combSym, ws)] st s) :
    TBL (s.syms combSym) ∈ s.rd ∧ (s.syms combSym).toNat + 49152 ≤ 2 ^ 64 ∧
      (∀ q < 64 * 96, s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q) ∧
      (∀ r ∈ s.wr, (TBL (s.syms combSym)).Disjoint r) ∧
      ∀ r ∈ PPC64LE.abi.reserved st s, (TBL (s.syms combSym)).Disjoint r := by
  have hrd := h.mem_rd List.mem_cons_self
  have hfit := h.fit List.mem_cons_self
  have hd : (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms combSym, 8 * ws.length⟩ r) ∧
      ∀ r ∈ PPC64LE.abi.reserved st s, Region.Disjoint ⟨s.syms combSym, 8 * ws.length⟩ r :=
    (h.2.2.1 _ List.mem_cons_self).2
  rw [hl] at hrd hfit hd
  refine ⟨hrd, hfit, fun q hq => ?_, hd.1, hd.2⟩
  rw [h.readW List.mem_cons_self (by rw [hl]; exact hq), hg q hq]

/-- What `abi.withConsts combConsts` says of the comb's table. -/
theorem tbl_of_consts {st : Nat} {s : State} (h : ConstsOk combConsts st s) :
    TBL (s.syms combSym) ∈ s.rd ∧ (s.syms combSym).toNat + 49152 ≤ 2 ^ 64 ∧
      (∀ q < 64 * 96, s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q) ∧
      (∀ r ∈ s.wr, (TBL (s.syms combSym)).Disjoint r) ∧
      ∀ r ∈ PPC64LE.abi.reserved st s, (TBL (s.syms combSym)).Disjoint r :=
  tbl_of_consts' combWords_length (fun _ hq => combWords_getD hq) h

/-- The readable regions under `abi.withConsts [(combSym, ws)]`: those without it, then the table. -/
theorem rd_of_consts' {st : Nat} {s : State} {ws : List (BitVec 64)} {L : List Region}
    (hl : ws.length = 64 * 96) (h : ConstsOk [(combSym, ws)] st s)
    (hL : s.rd.take (s.rd.length - 1) = L) : s.rd = L ++ [TBL (s.syms combSym)] := by
  have h1 := h.1
  simp only [List.length_singleton, constRegs, Abi.constRegions, List.map_cons, List.map_nil, hl] at h1
  calc s.rd = s.rd.take (s.rd.length - 1) ++ s.rd.drop (s.rd.length - 1) := (List.take_append_drop _ _).symm
    _ = L ++ [TBL (s.syms combSym)] := by rw [hL, h1]

theorem rd_of_consts {st : Nat} {s : State} {L : List Region} (h : ConstsOk combConsts st s)
    (hL : s.rd.take (s.rd.length - 1) = L) : s.rd = L ++ [TBL (s.syms combSym)] :=
  rd_of_consts' combWords_length h hL

/-- `BasePre` on entry to a call of `vg_ed25519_scalar_base`. -/
theorem basePre_call {t : State} {o p w T : Addr} (h3 : t.gpr .r3 = o) (h4 : t.gpr .r4 = p)
    (h5 : t.gpr .r5 = w) (hsy : t.syms combSym = T)
    (oW : (⟨o, 32⟩ : Region).Disjoint ⟨w, 8192⟩) (pW : (⟨p, 32⟩ : Region).Disjoint ⟨w, 8192⟩)
    (tfit : T.toNat + 49152 ≤ 2 ^ 64)
    (words : ∀ q < 64 * 96, t.mem.readW (T + BitVec.ofNat 64 (8 * q)) 64 = combWord q)
    (tW : (TBL T).Disjoint ⟨w, 8192⟩) :
    BasePre (t.callEntry.withRegions [⟨p, 32⟩, TBL T] [⟨o, 32⟩, ⟨w, 8192⟩]) := by
  have e3 : (t.callEntry.withRegions [⟨p, 32⟩, TBL T] [⟨o, 32⟩, ⟨w, 8192⟩]).gpr .r3 = o := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h3]
  have e4 : (t.callEntry.withRegions [⟨p, 32⟩, TBL T] [⟨o, 32⟩, ⟨w, 8192⟩]).gpr .r4 = p := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h4]
  have e5 : (t.callEntry.withRegions [⟨p, 32⟩, TBL T] [⟨o, 32⟩, ⟨w, 8192⟩]).gpr .r5 = w := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h5]
  have es : (t.callEntry.withRegions [⟨p, 32⟩, TBL T] [⟨o, 32⟩, ⟨w, 8192⟩]).syms combSym = T := hsy
  have em : (t.callEntry.withRegions [⟨p, 32⟩, TBL T] [⟨o, 32⟩, ⟨w, 8192⟩]).mem = t.mem := rfl
  exact ⟨by rw [e4, es]; rfl, by rw [e3, e5]; rfl, by rw [e3, e5]; exact oW,
    by rw [e4, e5]; exact pW, by rw [es]; exact tfit,
    fun q hq => by rw [em, es]; exact words q hq, by rw [es, e5]; exact tW⟩

/-- A contract by register `kR` without the comb's table implies the signature's contract under
`abi`; so does it with the table, under `abi.withConsts combConsts`. -/
theorem consts_implies {kR : Contract isa} {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {st : Nat}
    (h : kR.Implies (sig.contract abi pre post wa st))
    (hpost : ∀ s s', kR.post s s' → kR.post (stripConsts combConsts s) s')
    (hpub : ∀ s₁ s₂, kR.pub (stripConsts combConsts s₁) (stripConsts combConsts s₂) → kR.pub s₁ s₂)
    (hsat : ∃ s, (sig.contract (abi.withConsts combConsts) pre post wa st).pre s) :
    Contract.Implies (M := isa)
      { pre := fun s => kR.pre (stripConsts combConsts s) ∧ ConstsOk combConsts st s
        post := kR.post
        pub := fun s₁ s₂ => kR.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym }
      (sig.contract (abi.withConsts combConsts) pre post wa st) where
  pre _ hs := ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (post_stripConsts.mp (h.post (stripConsts combConsts s) s'
    (pre_consts.mp hs).1 (hpost s s' hp)))
  pub s₁ s₂ h₁ h₂ hp := ⟨hpub _ _ (h.pub (stripConsts combConsts s₁) (stripConsts combConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_stripConsts.mpr (pub_consts.mp hp).1)),
    (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := hsat

end VG.Proof.Ed25519.PPC64LE
