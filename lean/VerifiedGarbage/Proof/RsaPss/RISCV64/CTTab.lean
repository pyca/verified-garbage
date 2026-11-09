module

-- separate module: it builds in parallel with the correctness proofs, which `CTHash` does not need.

public import VerifiedGarbage.Proof.RsaPss.RISCV64.TabCall
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTMgfT
import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT

/-!
# RSASSA-PSS on RISC-V: the calls through the table of `MdHash`, twice

Untrusted: everything here is checked by Lean. As the calls through a table
of `Hash` (`Proof/RsaOaep/RISCV64/CTMgfT.lean`), for the table of `MdHash`
that is our stack argument `j` (`TabM`): two runs compared through anchors
`an x` (`BT`), whose entry states' tables are at the anchor's address and
hold the anchor's addresses of `H`'s functions, its compression function and
the digest (`TabAM`), load the same words of it (`twordM_two`) and so call
the same function (`tcallM_two`); its streaming functions by `init_ct`,
`upd_ct` and `fin_ct` (`initM_two`, `updM_two`, `finM_two`), the
compression function and the digest by their contracts (`compM_two`,
`digM_two`, `RelCT.callEx`), with the same arguments in both runs.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes oSt oDig oRsa tword tcall)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits off fr OkS BT BT.b B.spS Base.spA HashCT init_ct upd_ct fin_ct UpdArgs
  FinArgs sc_cov sdis hfits offs twA_taint twB_taint)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post wp_ld wp_addSp wp_nil)
open VG.Proof.MdHashTable.RISCV64 (digestK)
open VG.Impl.MdHashTable.RISCV64 (digest)

/-- What each run's entry and the anchor have of the table of `MdHash` that
is our stack argument `j`: the table, at the anchor's address, with the
anchor's addresses of its functions. -/
structure TabAM {H : Hash} {hH : HashOK H} (M : MdL H hH) (dN : String) (f : MdFns) (j : Nat)
    (S : State → Addr) (Pre : State → Prop) (Pub : State → State → Prop) : Prop where
  tab : ∀ {s}, Pre s → TabM M dN f j S s (stackArg s j)
  arg : ∀ {a s}, Pub a s → stackArg s j = stackArg a j
  ai : ∀ {a s}, Pub a s → s.syms H.initN = a.syms H.initN
  au : ∀ {a s}, Pub a s → s.syms H.updN = a.syms H.updN
  af : ∀ {a s}, Pub a s → s.syms H.finN = a.syms H.finN
  ac : ∀ {a s}, Pub a s → s.syms M.compN = a.syms M.compN
  ad : ∀ {a s}, Pub a s → s.syms dN = a.syms dN

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : OkS S Pre Pub) {H : Hash} {hH : HashOK H} {M : MdL H hH} {dN : String} {f : MdFns} {j : Nat}
  (A : TabAM M dN f j S Pre Pub) {α : Type} {an : α → State}

include X A in
/-- The load of the table's word `k` into `t1`, which is `v` of the anchor
in every run. -/
theorem twordM_two {Φ : α → State → Prop} (hb : ∀ x t, Φ x t → BT S vf Pre Pub (an x) t) {k : Nat}
    (hk : k < 5) {v : State → BitVec 64}
    (hv : ∀ {a s}, Pre s → Pub a s → s.mem.readW (stackArg s j + BitVec.ofNat 64 (8 * k)) 64 = v a) :
    RelCT isa (Two Φ) (.block (tword .t1 j k))
      (Two fun x u => ∃ t, Φ x t ∧ Only [.t1] t u ∧ u.syms = t.syms ∧ u.gpr .t1 = v (an x)) := by
  have hd : Reg.t1 = .a6 ∨ Reg.t1 = .t1 ∨ Reg.t1 = .a0 := .inr (.inl rfl)
  let Ψ₁ := fun (x : α) u => ∃ t, Φ x t ∧ Only [.t1] t u ∧ u.syms = t.syms ∧ u.gpr .t1 = stackArg (an x) j
  show RelCT isa _ (.block ([.addSp .t1 (frameBytes + 8 * j), .load .d .t1 .t1 0] ++ [.load .d .t1 .t1 (8 * k)])) _
  refine RelCT.block_append (RelCT.seq (two_post (Ψ := Ψ₁) (twA_taint j hd fun x t₁ t₂ h₁ h₂ =>
      ⟨((hb x t₁ h₁).b.spS X).trans ((hb x t₂ h₂).b.spS X).symm, fun _ h => nomatch h⟩) fun x t h => ?_)
    (two_post (twB_taint (8 * k) hd fun x u₁ u₂ ⟨t₁, h₁, o₁, _, e₁⟩ ⟨t₂, h₂, o₂, _, e₂⟩ =>
      ⟨by rw [o₁.sp, o₂.sp]; exact ((hb x t₁ h₁).b.spS X).trans ((hb x t₂ h₂).b.spS X).symm, fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂]⟩) fun x u ⟨t, h, o, sy, e⟩ => ?_))
  · obtain ⟨s, P, p, b, _⟩ := hb x t h
    have T := A.tab P
    refine WP.of_syms (wp_addSp (h := T.jo) fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s j)
      (by rw [e₁, b.sp, ← Proof.RsaOaep.RISCV64.stackArgAddr_fb]; simp) T.argA
      (by rw [o₁.rd, b.rd]; exact let ⟨R, hR, hc⟩ := T.argR; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₂ o₂ e₂ => wp_nil fun sy₂ => ⟨t, h, (o₁.trans o₂).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr, sy₂, by
          rw [e₂, o₁.mem, b.readW_apart T.argK T.argS, ← A.arg p]; rfl⟩))
  · obtain ⟨s, P, p, b, sy₀⟩ := hb x t h
    have T := A.tab P
    refine WP.of_syms (wp_ld (a := stackArg s j + BitVec.ofNat 64 (8 * k)) (by rw [e, A.arg p]) (T.wA hk)
      (by rw [o.rd, b.rd]; exact let ⟨R, hR, hc⟩ := T.tR k hk; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₂ o₂ e₂ => wp_nil fun sy₂ => ⟨t, h, (o.trans o₂).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr, sy₂.trans sy, by
          rw [e₂, o.mem, b.readW_apart (T.tK k hk) (T.tS k hk), hv P p]⟩) (by omega))

include X A in
/-- The call of the table's function `k`, among `ts`, which reaches `n` in
every run, at the anchor's address of `n`, as the call of `n` from the
states the load of its address leaves. -/
theorem tcallM_two {Φ : α → State → Prop} (hb : ∀ x t, Φ x t → BT S vf Pre Pub (an x) t) {k : Nat}
    (hk : k < 5) {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hn : ∀ {a s}, Pre s → Pub a s → ts.find? (fun q => s.syms q.1 == s.syms n) = some (n, c) ∧
      s.mem.readW (stackArg s j + BitVec.ofNat 64 (8 * k)) 64 = s.syms n ∧ s.syms n = a.syms n)
    (hcall : RelCT isa (Two fun x u => ∃ t, Φ x t ∧ Only [.t1] t u ∧ u.syms = t.syms) (.call n c)
      fun _ _ => True) :
    RelCT isa (Two Φ) (tcall j k ts) fun _ _ => True := by
  refine RelCT.seq (twordM_two X A hb (k := k) hk (v := fun a => a.syms n)
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
        u.gpr .t1 = (an x).syms n → icallTarget isa u ((an x).syms n) (q :: ts) = some (n, c) :=
      fun {u t s} y z P p _ => by
        show (q :: ts).find? (fun q => u.syms q.1 == (an x).syms n) = _
        rw [y, z, ← (hn P p).2.2]; exact (hn P p).1
    exact ⟨(an x).syms n, by show some (u₁.gpr .t1) = _; rw [e₁], by show some (u₂.gpr .t1) = _; rw [e₂],
      tg y₁ z₁ P₁ p₁ e₁, tg y₂ z₂ P₂ p₂ e₂, rfl⟩

include X in
/-- A state after the load of a function's address keeps `BT`. -/
theorem bt_t1 {a t u : State} (h : BT S vf Pre Pub a t) (o : Only [.t1] t u) (y : u.syms = t.syms) :
    BT S vf Pre Pub a u :=
  let ⟨s, P, p, b, sy⟩ := h; ⟨s, P, p, b.only (X.fits P) o, y.trans sy⟩

theorem only_t1 {t u : State} (o : Only [.t1] t u) {r : Reg} (hr : r ≠ .t1 := by decide) : u.gpr r = t.gpr r :=
  o.gpr r fun h => hr (List.mem_singleton.mp h)

variable (cH : HashCT hH) (hF : H.F ≤ 208)

include X A cH in
/-- `init` through the table, on the state at `S + oSt`, in both runs. -/
theorem initM_two {Φ : α → State → Prop}
    (h : ∀ x t, Φ x t → BT S vf Pre Pub (an x) t ∧ t.gpr .a0 = off (S (an x)) oSt) :
    RelCT isa (Two Φ) (tcall j 0 f.init) fun _ _ => True :=
  tcallM_two X A (fun x t hp => (h x t hp).1) (k := 0) (by decide)
    (fun P p => ⟨(A.tab P).ok.i, by rw [Nat.mul_zero, BitVec.add_zero]; exact (A.tab P).mem.1, A.ai p⟩)
    (init_ct (S := S) (vf := vf) cH fun u₁ u₂ ⟨x, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ => by
      obtain ⟨b₁, e₁⟩ := h x t₁ h₁
      obtain ⟨b₂, e₂⟩ := h x t₂ h₂
      obtain ⟨s₁, P₁, p₁, c₁, -⟩ := bt_t1 X b₁ o₁ y₁
      obtain ⟨s₂, P₂, p₂, c₂, -⟩ := bt_t1 X b₂ o₂ y₂
      exact ⟨s₁, s₂, X.fits P₁, c₁, by rw [only_t1 o₁, e₁, X.S p₁], X.fits P₂, c₂, by rw [only_t1 o₂, e₂, X.S p₂],
        by rw [only_t1 o₁, only_t1 o₂, e₁, e₂], (Base.spA X p₁ c₁).trans (Base.spA X p₂ c₂).symm⟩)

include X A cH hF in
/-- `update` through the table, in both runs with the same arguments. -/
theorem updM_two {Φ : α → State → Prop}
    (h : ∀ x t, Φ x t → ∃ s d l, Pre s ∧ Pub (an x) s ∧ UpdArgs S vf H s t d l ∧ t.syms = s.syms)
    (hr : ∀ x t₁ t₂, Φ x t₁ → Φ x t₂ → ∀ r ∈ [Reg.a0, .a1, .a2, .a3], t₁.gpr r = t₂.gpr r) :
    RelCT isa (Two Φ) (tcall j 1 f.upd) fun _ _ => True := by
  have ua : ∀ {x : α} {t u : State}, Φ x t → Only [.t1] t u →
      ∃ s d l, UpdArgs S vf H s u d l ∧ Pub (an x) s := fun {x t u} hp o => by
    obtain ⟨s, d, l, P, p, A', -⟩ := h x t hp
    exact ⟨s, d, l, ⟨A'.P, A'.b.only A'.P o, by rw [only_t1 o]; exact A'.h0, by rw [only_t1 o]; exact A'.h2,
      by rw [only_t1 o]; exact A'.h3, by rw [o.rd, o.wr]; exact A'.hdc, A'.hd₁, A'.hd₃⟩, p⟩
  refine tcallM_two X A (fun x t hp => let ⟨s, _, _, P, p, A', y⟩ := h x t hp; ⟨s, P, p, A'.b, y⟩) (k := 1)
    (by decide) (fun P p => ⟨(A.tab P).ok.u, by rw [Nat.mul_one]; exact (A.tab P).mem.2.1, A.au p⟩)
    (upd_ct (S := S) (vf := vf) cH hF fun u₁ u₂ ⟨x, ⟨t₁, h₁, o₁, _⟩, ⟨t₂, h₂, o₂, _⟩⟩ => ?_)
  obtain ⟨s₁, d₁, l₁, A₁, p₁⟩ := ua h₁ o₁
  obtain ⟨s₂, d₂, l₂, A₂, p₂⟩ := ua h₂ o₂
  refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hq => ?_, (Base.spA X p₁ A₁.b).trans (Base.spA X p₂ A₂.b).symm⟩
  rw [o₁.gpr r (by revert r; decide), o₂.gpr r (by revert r; decide)]
  exact hr x t₁ t₂ h₁ h₂ r hq

include X A cH hF in
/-- `finalize` through the table, in both runs with the same arguments. -/
theorem finM_two {Φ : α → State → Prop}
    (h : ∀ x t, Φ x t → ∃ s, Pre s ∧ Pub (an x) s ∧ FinArgs S vf s t ∧ t.syms = s.syms)
    (hr : ∀ x t₁ t₂, Φ x t₁ → Φ x t₂ → ∀ r ∈ [Reg.a0, .a1, .a2], t₁.gpr r = t₂.gpr r) :
    RelCT isa (Two Φ) (tcall j 2 f.fin) fun _ _ => True := by
  have fa : ∀ {x : α} {t u : State}, Φ x t → Only [.t1] t u → ∃ s, FinArgs S vf s u ∧ Pub (an x) s :=
    fun {x t u} hp o => by
      obtain ⟨s, P, p, A', -⟩ := h x t hp
      exact ⟨s, ⟨A'.P, A'.b.only A'.P o, by rw [only_t1 o]; exact A'.h0, by rw [only_t1 o]; exact A'.h2⟩, p⟩
  refine tcallM_two X A (fun x t hp => let ⟨s, P, p, A', y⟩ := h x t hp; ⟨s, P, p, A'.b, y⟩) (k := 2)
    (by decide) (fun P p => ⟨(A.tab P).ok.fi, by rw [show 8 * 2 = 16 from rfl]; exact (A.tab P).mem.2.2.1, A.af p⟩)
    (fin_ct (S := S) (vf := vf) cH hF fun u₁ u₂ ⟨x, ⟨t₁, h₁, o₁, _⟩, ⟨t₂, h₂, o₂, _⟩⟩ => ?_)
  obtain ⟨s₁, A₁, p₁⟩ := fa h₁ o₁
  obtain ⟨s₂, A₂, p₂⟩ := fa h₂ o₂
  refine ⟨s₁, s₂, A₁, A₂, fun r hq => ?_, (Base.spA X p₁ A₁.b).trans (Base.spA X p₂ A₂.b).symm⟩
  rw [o₁.gpr r (by revert r; decide), o₂.gpr r (by revert r; decide)]
  exact hr x t₁ t₂ h₁ h₂ r hq

/-- What a call of the compression function needs, in a run from the entry
state `s`: the `n` blocks at `S + o`. -/
structure CompArgs (S : State → Addr) (vf : State → Reg → BitVec 64) (s t : State) (o n : Nat) : Prop where
  P : Fits S s
  b : Base S vf s t
  al : (S s).toNat % 8 = 0
  h0 : t.gpr .a0 = off (S s) oSt
  h1 : t.gpr .a1 = off (S s) o
  h2 : t.gpr .a2 = BitVec.ofNat 64 n
  h3 : t.gpr .a3 = off (S s) oCs
  ho : oCs + 144 ≤ o

include X A in
/-- The compression function through the table, in both runs with the same
arguments. -/
theorem compM_two {Φ : α → State → Prop}
    (h : ∀ x t, Φ x t → ∃ s o n, Pre s ∧ Pub (an x) s ∧ CompArgs S vf s t o n ∧ o + H.B * n ≤ oRsa ∧
      t.syms = s.syms)
    (hr : ∀ x t₁ t₂, Φ x t₁ → Φ x t₂ → ∀ r ∈ [Reg.a0, .a1, .a2, .a3], t₁.gpr r = t₂.gpr r) :
    RelCT isa (Two Φ) (tcall j 3 f.comp) fun _ _ => True := by
  have hN := hH.hN
  have hcs := M.hcs
  have hY : oCs = 1664 := rfl
  obtain ⟨_, hSt, _, _, hRs⟩ := offs
  have ca : ∀ {x : α} {t u : State}, Φ x t → Only [.t1] t u →
      ∃ s o n, CompArgs S vf s u o n ∧ o + H.B * n ≤ oRsa ∧ Pub (an x) s := fun {x t u} hp oo => by
    obtain ⟨s, o, n, P, p, C, hon, -⟩ := h x t hp
    exact ⟨s, o, n, ⟨C.P, C.b.only C.P oo, C.al, by rw [only_t1 oo]; exact C.h0, by rw [only_t1 oo]; exact C.h1,
      by rw [only_t1 oo]; exact C.h2, by rw [only_t1 oo]; exact C.h3, C.ho⟩, hon, p⟩
  have pre : ∀ {s u : State} {o n : Nat}, CompArgs S vf s u o n → o + H.B * n ≤ oRsa →
      (compK M.md M.cs).pre (u.callEntry.withRegions [⟨off (S s) o, H.B * n⟩]
        [⟨off (S s) oSt, H.N⟩, ⟨off (S s) oCs, M.cs⟩]) := fun {s u o n} C hon => by
    have hn : n < 2 ^ 64 := by
      have : n ≤ H.B * n := Nat.le_mul_of_pos_left n (Nat.two_pow_pos _)
      unfold oRsa at hon; omega
    have c0 : u.callEntry.gpr .a0 = off (S s) oSt := (State.callEntry_gpr _ (by decide)).trans C.h0
    have c1 : u.callEntry.gpr .a1 = off (S s) o := (State.callEntry_gpr _ (by decide)).trans C.h1
    have c2 : u.callEntry.gpr .a2 = BitVec.ofNat 64 n := (State.callEntry_gpr _ (by decide)).trans C.h2
    have c3 : u.callEntry.gpr .a3 = off (S s) oCs := (State.callEntry_gpr _ (by decide)).trans C.h3
    have e2 : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    have ho := C.ho
    simp only [compK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1, c2, c3, e2]
    refine ⟨trivial, trivial, sdis (.inl (by omega)) (by omega) (by omega), sdis (.inr (by omega)) hon (by omega),
      sdis (.inr (by omega)) hon (by omega), ?_⟩
    have e : (off (S s) oCs).toNat = (S s).toNat + oCs := by
      have := C.P.wS
      simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    show (off (S s) oCs).toNat % 8 = 0
    rw [e]; have := C.al; omega
  have cov : ∀ {s u : State} {o n : Nat}, CompArgs S vf s u o n → o + H.B * n ≤ oRsa →
      Covers ([⟨off (S s) o, H.B * n⟩] ++ [⟨off (S s) oSt, H.N⟩, ⟨off (S s) oCs, M.cs⟩]) (u.rd ++ u.wr) ∧
        Covers [⟨off (S s) oSt, H.N⟩, ⟨off (S s) oCs, M.cs⟩] u.wr := fun {s u o n} C hon => by
    have hwc0 : Covers [⟨off (S s) oSt, H.N⟩, ⟨off (S s) oCs, M.cs⟩] (fr s :: s.wr) :=
      Covers.pair (sc_cov C.P (by omega)) (sc_cov C.P (by omega))
    rw [C.b.rd, C.b.wr]
    exact ⟨Covers.append_left (Covers.right (sc_cov C.P hon)) (Covers.right hwc0), hwc0⟩
  refine tcallM_two X A (fun x t hp => let ⟨s, _, _, P, p, C, _, y⟩ := h x t hp; ⟨s, P, p, C.b, y⟩) (k := 3)
    (by decide) (fun P p => ⟨(A.tab P).ok.c, by rw [show 8 * 3 = 24 from rfl]; exact (A.tab P).mem.2.2.2.1, A.ac p⟩)
    (RelCT.callEx M.comp M.compCT fun u₁ u₂ ⟨x, ⟨t₁, h₁, o₁, _⟩, ⟨t₂, h₂, o₂, _⟩⟩ => ?_)
  obtain ⟨s₁, q₁, n₁, C₁, l₁, p₁⟩ := ca h₁ o₁
  obtain ⟨s₂, q₂, n₂, C₂, l₂, p₂⟩ := ca h₂ o₂
  have g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3], u₁.gpr r = u₂.gpr r := fun r hq => by
    rw [o₁.gpr r (by revert r; decide), o₂.gpr r (by revert r; decide)]
    exact hr x t₁ t₂ h₁ h₂ r hq
  refine ⟨_, _, _, _, pre C₁ l₁, pre C₂ l₂, ?_, (cov C₁ l₁).1, (cov C₁ l₁).2, (cov C₂ l₂).1, (cov C₂ l₂).2⟩
  simp only [compK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide)]
  exact ⟨g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide),
    (Base.spA X p₁ C₁.b).trans (Base.spA X p₂ C₂.b).symm⟩

include X A in
/-- The digest through the table, of the hash value at `S + oSt` to
`S + oDig`, in both runs. -/
theorem digM_two {Φ : α → State → Prop}
    (h : ∀ x t, Φ x t → BT S vf Pre Pub (an x) t ∧ t.gpr .a0 = off (S (an x)) oSt ∧
      t.gpr .a1 = off (S (an x)) oDig) :
    RelCT isa (Two Φ) (tcall j 4 f.dig) fun _ _ => True := by
  have hN := hH.hN
  obtain ⟨_, hSt, hDg, _, _⟩ := offs
  refine tcallM_two X A (fun x t hp => (h x t hp).1) (k := 4) (by decide)
    (fun P p => ⟨(A.tab P).ok.d, by rw [show 8 * 4 = 32 from rfl]; exact (A.tab P).mem.2.2.2.2, A.ad p⟩)
    (RelCT.callEx (k := digestK M.md) (MdHashTable.RISCV64.digest_ok M.outOk)
      (MdHashTable.RISCV64.digest_ct_of M.outCT) fun u₁ u₂ ⟨x, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ => ?_)
  obtain ⟨b₁, x0, x1⟩ := h x t₁ h₁
  obtain ⟨b₂, z0, z1⟩ := h x t₂ h₂
  obtain ⟨s₁, P₁, p₁, c₁, -⟩ := bt_t1 X b₁ o₁ y₁
  obtain ⟨s₂, P₂, p₂, c₂, -⟩ := bt_t1 X b₂ o₂ y₂
  have pre : ∀ {s u : State}, Pre s → Pub (an x) s → Base S vf s u → u.gpr .a0 = off (S (an x)) oSt →
      u.gpr .a1 = off (S (an x)) oDig →
      (digestK M.md).pre (u.callEntry.withRegions [⟨off (S s) oSt, H.N⟩] [⟨off (S s) oDig, H.N⟩]) ∧
        Covers ([⟨off (S s) oSt, H.N⟩] ++ [⟨off (S s) oDig, H.N⟩]) (u.rd ++ u.wr) ∧
        Covers [⟨off (S s) oDig, H.N⟩] u.wr := fun {s u} P p b e0 e1 => by
    have c0 : u.callEntry.gpr .a0 = off (S s) oSt := (State.callEntry_gpr _ (by decide)).trans (by rw [e0, X.S p])
    have c1 : u.callEntry.gpr .a1 = off (S s) oDig := (State.callEntry_gpr _ (by decide)).trans (by rw [e1, X.S p])
    have hwc0 : Covers [⟨off (S s) oDig, H.N⟩] (fr s :: s.wr) := sc_cov (X.fits P) (by omega)
    simp only [digestK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1]
    rw [b.rd, b.wr]
    exact ⟨⟨trivial, trivial, sdis (.inl (by omega)) (by omega) (by omega)⟩,
      Covers.append_left (Covers.right (sc_cov (X.fits P) (by omega))) (Covers.right hwc0), hwc0⟩
  obtain ⟨q₁, v₁, w₁⟩ := pre P₁ p₁ c₁ (by rw [only_t1 o₁, x0]) (by rw [only_t1 o₁, x1])
  obtain ⟨q₂, v₂, w₂⟩ := pre P₂ p₂ c₂ (by rw [only_t1 o₂, z0]) (by rw [only_t1 o₂, z1])
  refine ⟨_, _, _, _, q₁, q₂, ?_, v₁, w₁, v₂, w₂⟩
  simp only [digestK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide)]
  exact ⟨by rw [only_t1 o₁, only_t1 o₂, x0, z0], by rw [only_t1 o₁, only_t1 o₂, x1, z1],
    (Base.spA X p₁ c₁).trans (Base.spA X p₂ c₂).symm⟩

end

end VG.Proof.RsaPss.RISCV64
