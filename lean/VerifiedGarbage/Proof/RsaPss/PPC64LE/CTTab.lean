module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.MComp
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMgfT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# RSASSA-PSS on PPC64LE: the hash function's table, in two runs

Untrusted: everything here is checked by Lean. As for MGF1's table of
`Hash` (`Proof/RsaOaep/PPC64LE/CTMgfT.lean`), for the hash function's table
of `MdHash`: what each run's entry and the anchor have of it (`MdTabA`), the
loads of its words (`tword_twoM`) and the calls through it (`tcall_twoM`),
which leak alike since both tables are at the anchor's address and hold the
anchor's addresses of the same functions; and the calls of the compression
function (`comp_ct`) and of the digest (`dig_ct`) with the same arguments, by
their contracts' constant time.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.RsaPss.PPC64LE (MdFns oY oSel)
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.MdHashTable.PPC64LE (digestK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits off fx hiRegs OkS BT B sc_cov sdis cR_dis twA_taint twB_taint
  stackArgAddr_fb)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two two_post wp_addSp wp_ld wp_nil)

/-- The tables' hash functions and their functions, which the proofs take:
MGF1's `G` with the functions `g` of the tables of `Hash`, and the hash
function `H`, whose compression function `cn` (of code `cc`) and digest `dn`
(of code `dc`) its table names, with the functions `f` of the tables of
`MdHash`. -/
structure Tabs where
  G : Hash
  g : Impl.RsaOaep.PPC64LE.Fns
  H : Hash
  cn : String
  cc : Prog isa
  dn : String
  dc : Prog isa
  f : MdFns

/-- What each run's entry and the anchor have of the hash function's table
that is our stack argument `j`: in each run the table, at the stack
argument, at the anchor's address and with the anchor's addresses of the
functions it names. -/
structure MdTabA (H : Hash) (cn : String) (cc : Prog isa) (dn : String) (dc : Prog isa) (f : MdFns) (j : Nat)
    (S : State → Addr) (Pre : State → Prop) (Pub : State → State → Prop) : Prop where
  tab : ∀ {s}, Pre s → MdTabS H cn cc dn dc f j S s (stackArg s j)
  arg : ∀ {a s}, Pub a s → stackArg s j = stackArg a j
  ai : ∀ {a s}, Pub a s → s.syms H.initN = a.syms H.initN
  au : ∀ {a s}, Pub a s → s.syms H.updN = a.syms H.updN
  af : ∀ {a s}, Pub a s → s.syms H.finN = a.syms H.finN
  ac : ∀ {a s}, Pub a s → s.syms cn = a.syms cn
  ad : ∀ {a s}, Pub a s → s.syms dn = a.syms dn

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : OkS S Pre Pub) {H : Hash} {cn dn : String} {cc dc : Prog isa} {f : MdFns} {j : Nat}
  (A : MdTabA H cn cc dn dc f j S Pre Pub)

include X A in
/-- The load of the table's word `k` into `r12`, which is `v` of the anchor
in every run. -/
theorem tword_twoM {α : Type} {Φ : α → State → Prop} {an : α → State} (hb : ∀ x t, Φ x t → BT S vf Pre Pub (an x) t)
    {k : Nat} (hk : k < 11) {v : State → BitVec 64}
    (hv : ∀ {a s}, Pre s → Pub a s → s.mem.readW (stackArg s j + BitVec.ofNat 64 (8 * k)) 64 = v a) :
    RelCT isa (Two Φ) (.block (tword .r12 j k))
      (Two fun x u => ∃ t, Φ x t ∧ Only [.r12] t u ∧ u.syms = t.syms ∧ u.gpr .r12 = v (an x)) := by
  let Ψ₁ := fun (x : α) u => ∃ t, Φ x t ∧ Only [.r12] t u ∧ u.syms = t.syms ∧ u.gpr .r12 = stackArg (an x) j
  show RelCT isa _ (.block ([.addSp .r12 0, .load .d .r12 .r12 (arg j)] ++ [.load .d .r12 .r12 (8 * k)])) _
  refine RelCT.block_append (RelCT.seq (two_post (Ψ := Ψ₁) (twA_taint j (.inr (.inl rfl)) fun x t₁ t₂ h₁ h₂ =>
      ⟨((hb x t₁ h₁).b.spS X).trans ((hb x t₂ h₂).b.spS X).symm, fun _ h => nomatch h⟩) fun x t h => ?_)
    (two_post (twB_taint (8 * k) (.inr (.inl rfl)) fun x u₁ u₂ ⟨t₁, h₁, o₁, _, e₁⟩ ⟨t₂, h₂, o₂, _, e₂⟩ =>
      ⟨by rw [o₁.sp, o₂.sp]; exact ((hb x t₁ h₁).b.spS X).trans ((hb x t₂ h₂).b.spS X).symm, fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂]⟩) fun x u ⟨t, h, o, sy, e⟩ => ?_))
  · obtain ⟨s, P, p, b, _⟩ := hb x t h
    have T := A.tab P
    refine WP.of_syms (wp_addSp fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s j)
      (by rw [e₁, b.sp, BitVec.add_zero, stackArgAddr_fb])
      (by rw [o₁.rd, b.rd]; exact let ⟨R, hR, hc⟩ := T.argR; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₂ o₂ e₂ => wp_nil fun sy₂ => ⟨t, h, (o₁.trans o₂).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr, sy₂, by
          rw [e₂, o₁.mem, b.readW_apart T.argK T.argS, ← A.arg p]; rfl⟩) (by decide) T.jo)
  · obtain ⟨s, P, p, b, sy₀⟩ := hb x t h
    have T := A.tab P
    refine WP.of_syms (wp_ld (a := stackArg s j + BitVec.ofNat 64 (8 * k)) (by rw [e, A.arg p])
      (by rw [o.rd, b.rd]; exact let ⟨R, hR, hc⟩ := T.tR k hk; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₂ o₂ e₂ => wp_nil fun sy₂ => ⟨t, h, (o.trans o₂).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr, sy₂.trans sy, by
          rw [e₂, o.mem, b.readW_apart (T.tK k hk) (T.tS k hk), hv P p]⟩) (by decide) (by omega))

include X A in
/-- The call of the table's function `k`, among `ts`, which reaches `n` in
every run, at the anchor's address of `n`. -/
theorem tcall_twoM {α : Type} {Φ : α → State → Prop} {an : α → State} (hb : ∀ x t, Φ x t → BT S vf Pre Pub (an x) t)
    {k : Nat} (hk : k < 5) {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hn : ∀ {a s}, Pre s → Pub a s → ts.find? (fun q => s.syms q.1 == s.syms n) = some (n, c) ∧
      s.mem.readW (stackArg s j + BitVec.ofNat 64 (8 * k)) 64 = s.syms n ∧ s.syms n = a.syms n)
    (hcall : RelCT isa (Two fun x u => ∃ t, Φ x t ∧ Only [.r12] t u ∧ u.syms = t.syms) (.call n c)
      fun _ _ => True) :
    RelCT isa (Two Φ) (tcall j k ts) fun _ _ => True := by
  refine RelCT.seq (tword_twoM X A hb (k := k) (by omega) (v := fun a => a.syms n)
    fun P p => (hn P p).2.1.trans (hn P p).2.2) ?_
  cases ts with
  | nil =>
    exact RelCT.of_false fun s₁ s₂ ⟨x, ⟨t, h, _⟩, _⟩ => by
      obtain ⟨s, P, p, _⟩ := hb x t h
      simpa using (hn P p).1
  | cons q ts =>
    refine RelCT.icalls_of_call (hcall.mono (fun _ _ ⟨x, ⟨t₁, h₁, o₁, y₁, _⟩, ⟨t₂, h₂, o₂, y₂, _⟩⟩ =>
      ⟨x, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩) fun _ _ h => h) ?_
    rintro u₁ u₂ ⟨x, ⟨t₁, h₁, o₁, y₁, e₁⟩, ⟨t₂, h₂, o₂, y₂, e₂⟩⟩
    obtain ⟨s₁, P₁, p₁, -, z₁⟩ := hb x t₁ h₁
    obtain ⟨s₂, P₂, p₂, -, z₂⟩ := hb x t₂ h₂
    have tg : ∀ {u t s : State}, u.syms = t.syms → t.syms = s.syms → Pre s → Pub (an x) s →
        u.gpr .r12 = (an x).syms n → icallTarget isa u ((an x).syms n) (q :: ts) = some (n, c) :=
      fun {u t s} y z P p _ => by
        show (q :: ts).find? (fun q => u.syms q.1 == (an x).syms n) = _
        rw [y, z, ← (hn P p).2.2]; exact (hn P p).1
    exact ⟨(an x).syms n, by show some (u₁.gpr .r12) = _; rw [e₁], by show some (u₂.gpr .r12) = _; rw [e₂],
      tg y₁ z₁ P₁ p₁ e₁, tg y₂ z₂ P₂ p₂ e₂, rfl⟩

end

/-! ## The compression function and the digest, in two runs -/

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {P : Params} {md : Md P.B P.N P.L}

/-- What a call of the compression function needs, in a run from the entry
state `s`: the block at `oY + b`. -/
structure CompArgs (S : State → Addr) (vf : State → Reg → BitVec 64) (P : Params) (s t : State) (b : Nat) : Prop where
  F : Fits S s
  base : Base S vf s t
  h3 : t.gpr .r3 = off (S s) oSt
  h4 : t.gpr .r4 = off (S s) (oY + b)
  h5 : t.gpr .r5 = BitVec.ofNat 64 1
  h6 : t.gpr .r6 = off (S s) oW
  hb : b + P.B ≤ 2048
  hN : P.N ≤ 64
  hso : P.so ≤ 1024

/-- The compression function, in both runs, with the same arguments. -/
theorem comp_ct {cn : String} {cc : Prog isa} (hc : CalleeOk md cc)
    (hct : ConstantTime isa (compressK md).pre (compressK md).pub cc) {Q : State → State → Prop}
    (hP : ∀ t₁ t₂, Q t₁ t₂ → ∃ s₁ s₂ b₁ b₂, CompArgs S vf P s₁ t₁ b₁ ∧ CompArgs S vf P s₂ t₂ b₂ ∧
      (∀ r ∈ [Reg.r3, .r4, .r5, .r6], t₁.gpr r = t₂.gpr r) ∧ t₁.sp = t₂.sp) :
    RelCT isa Q (.call cn cc) fun _ _ => True := by
  have hR : oRsa = 8192 := rfl
  have hY : oY = 2560 := rfl
  have hSt : oSt = 1024 := rfl
  have hW : oW = 1352 := rfl
  refine RelCT.callEx hc.verified hct fun t₁ t₂ hp => ?_
  obtain ⟨s₁, s₂, b₁, b₂, A₁, A₂, eg, esp⟩ := hP t₁ t₂ hp
  have pre : ∀ {s t : State} {b : Nat}, CompArgs S vf P s t b →
      (compressK md).pre (t.callEntry.withRegions [⟨off (S s) (oY + b), P.B⟩]
        [⟨off (S s) oSt, P.N⟩, ⟨off (S s) oW, P.so⟩]) := fun {s t b} A => by
    have hB1 : P.B * (BitVec.ofNat 64 1).toNat = P.B := by simp
    have := A.hb; have := A.hN; have := A.hso
    simp only [compressK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
      A.h3, A.h4, A.h5, A.h6, hB1]
    exact ⟨trivial, trivial, sdis (.inl (by omega)) (by omega) (by omega), sdis (.inr (by omega)) (by omega) (by omega),
      sdis (.inr (by omega)) (by omega) (by omega)⟩
  have cov : ∀ {s t : State} {b : Nat}, CompArgs S vf P s t b →
      Covers ([⟨off (S s) (oY + b), P.B⟩] ++ [⟨off (S s) oSt, P.N⟩, ⟨off (S s) oW, P.so⟩]) (t.rd ++ t.wr) ∧
        Covers [⟨off (S s) oSt, P.N⟩, ⟨off (S s) oW, P.so⟩] t.wr := fun {s t b} A => by
    have := A.hb; have := A.hN; have := A.hso
    have hcw : Covers [⟨off (S s) oSt, P.N⟩, ⟨off (S s) oW, P.so⟩] t.wr := by
      rw [A.base.wr]; exact Covers.pair (sc_cov A.F (by omega)) (sc_cov A.F (by omega))
    exact ⟨Covers.append_left (Covers.right (by rw [A.base.wr]; exact sc_cov A.F (by omega))) (Covers.right hcw), hcw⟩
  refine ⟨_, _, _, _, pre A₁, pre A₂, ?_, (cov A₁).1, (cov A₁).2, (cov A₂).1, (cov A₂).2⟩
  simp only [compressK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
  simp only [State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide)]
  exact ⟨eg _ (by decide), eg _ (by decide), eg _ (by decide), eg _ (by decide), esp⟩

/-- What a call of the digest needs, in a run from the entry state `s`. -/
structure DigArgs (S : State → Addr) (vf : State → Reg → BitVec 64) (P : Params) (s t : State) : Prop where
  F : Fits S s
  base : Base S vf s t
  h3 : t.gpr .r3 = off (S s) oSel
  h4 : t.gpr .r4 = off (S s) oDig
  hN : P.N ≤ 64

/-- The digest, in both runs, with the same arguments. -/
theorem dig_ct {dn : String} {dc : Prog isa}
    (hd : ∀ u, (digestK md).pre u → ∃ t u', Exec isa dc u t u' ∧ abiPreserved u u' ∧ (digestK md).post u u')
    (hct : ConstantTime isa (digestK md).pre (digestK md).pub dc) {Q : State → State → Prop}
    (hP : ∀ t₁ t₂, Q t₁ t₂ → ∃ s₁ s₂, DigArgs S vf P s₁ t₁ ∧ DigArgs S vf P s₂ t₂ ∧
      (∀ r ∈ [Reg.r3, .r4], t₁.gpr r = t₂.gpr r) ∧ t₁.sp = t₂.sp) :
    RelCT isa Q (.call dn dc) fun _ _ => True := by
  have hR : oRsa = 8192 := rfl
  have hDg : oDig = 1280 := rfl
  have hSl : oSel = 4800 := rfl
  refine RelCT.callEx hd hct fun t₁ t₂ hp => ?_
  obtain ⟨s₁, s₂, A₁, A₂, eg, esp⟩ := hP t₁ t₂ hp
  have pre : ∀ {s t : State}, DigArgs S vf P s t →
      (digestK md).pre (t.callEntry.withRegions [⟨off (S s) oSel, P.N⟩] [⟨off (S s) oDig, P.N⟩]) := fun {s t} A => by
    have := A.hN
    simp only [digestK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
      A.h3, A.h4]
    exact ⟨trivial, trivial, sdis (.inr (by omega)) (by omega) (by omega)⟩
  have cov : ∀ {s t : State}, DigArgs S vf P s t →
      Covers ([⟨off (S s) oSel, P.N⟩] ++ [⟨off (S s) oDig, P.N⟩]) (t.rd ++ t.wr) ∧
        Covers [⟨off (S s) oDig, P.N⟩] t.wr := fun {s t} A => by
    have := A.hN
    have hcw : Covers [⟨off (S s) oDig, P.N⟩] t.wr := by rw [A.base.wr]; exact sc_cov A.F (by omega)
    exact ⟨Covers.append_left (Covers.right (by rw [A.base.wr]; exact sc_cov A.F (by omega))) (Covers.right hcw), hcw⟩
  refine ⟨_, _, _, _, pre A₁, pre A₂, ?_, (cov A₁).1, (cov A₁).2, (cov A₂).1, (cov A₂).2⟩
  simp only [digestK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
  simp only [State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide)]
  exact ⟨eg _ (by decide), eg _ (by decide), esp⟩

end

end VG.Proof.RsaPss.PPC64LE
