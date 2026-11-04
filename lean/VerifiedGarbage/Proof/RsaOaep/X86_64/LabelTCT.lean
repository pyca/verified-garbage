module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfTCT
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfTCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP on x86-64: the label's hash with a table, in constant time

`hashLabelT f o` is constant time in two runs with the same frame, regions,
label's address and length, table and addresses of the hash function's
functions (`LQT`), whatever the label (`hashLabelT_ct`), as `hashLabel` is
(`hashLabel_ct`): each indirect call is to the same address in both runs,
and so of the same function (`Table.two_tcall`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs)
open VG.Impl.Mgf1.X86_64.Table (Fns tcall)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64 (two_taint two_ite)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)
open VG.Proof.RsaOaep.X86_64.Table (Tab TabAt TJ lay_keep11 initT_ok FnsGood tcall_good wp_gs two_tcall
  tload_taint)

/-- The label's hash's public data with a table: `LQ`, the table's address,
and the addresses of the hash function's `init`, `update` and `finalize`. -/
structure LQT extends LQ where
  p : Addr
  ai : Addr
  au : Addr
  af : Addr

/-- A point of `hashLabelT`: `LW`, the table's address in its slot, the
table, and the functions' addresses. -/
structure LWT (G : Stream) (f : Fns) (n : Nat) (q : LQT) (t : State) : Prop where
  lw : LW n q.toLQ t
  w35 : word t.mem q.F (8 * 35) = q.p
  tab : ∃ u₀ sArg, Tab G f q.F q.p sArg u₀ ∧ TJ u₀ q.F t ∧ t.rd = u₀.rd ∧ t.wr = u₀.wr
  ai : t.syms G.initN = q.ai
  au : t.syms G.updN = q.au
  af : t.syms G.finN = q.af

variable {G : Stream} {f : Fns} {n : Nat}

theorem LWT.tabAt {q : LQT} {t : State} (h : LWT G f n q t) : TabAt G f q.p t := by
  obtain ⟨u₀, _, T, J, rd, wr⟩ := h.tab
  exact T.at J rd wr

theorem LWT.w35' {q : LQT} {t : State} (h : LWT G f n q t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem q.F q.S V W) : W 35 = q.p := (R.fr 35 (by decide)).symm.trans h.w35

theorem LWT.congr {q : LQT} {t t' : State} (h : LWT G f n q t) (hsp : t'.gpr .rsp = t.gpr .rsp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem) (hs : t'.syms = t.syms) :
    LWT G f n q t' := by
  obtain ⟨u₀, sA, T, J, rd, wr⟩ := h.tab
  exact ⟨h.lw.congr hsp hrd hwr hm, by rw [hm]; exact h.w35, ⟨u₀, sA, T, J.ofMem hm hs, hrd.trans rd, hwr.trans wr⟩,
    by rw [hs]; exact h.ai, by rw [hs]; exact h.au, by rw [hs]; exact h.af⟩

theorem LWT.after {q : LQT} {t t' : State} (h : LWT G f n q t) (L' : Lay t' q.F q.S) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) {V V' : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem q.F q.S V W)
    (R' : Rep t'.mem q.F q.S V' W) (A : LabAt t q.F q.S W q.lab q.labLen)
    (hf : Frame (t.wr ++ [below (t.gpr .rsp) 16]) t.mem t'.mem) (hs : t'.syms = t.syms) : LWT G f n q t' := by
  obtain ⟨u₀, sA, T, J, rd, wr⟩ := h.tab
  exact ⟨h.lw.after L' hrd hwr R' A, by rw [R'.fr 35 (by decide), ← R.fr 35 (by decide)]; exact h.w35,
    ⟨u₀, sA, T, J.step wr h.lw.L.rsp hf hs, hrd.trans rd, hwr.trans wr⟩, by rw [hs]; exact h.ai,
    by rw [hs]; exact h.au, by rw [hs]; exact h.af⟩

variable (hG : StreamOK G)

include hG in
/-- The label's hash to `scratch + o` with the table's hash function, in two
runs with the same `LQT`. -/
theorem hashLabelT_ct (hgi : FnsGood f.init) (hgu : FnsGood f.upd) (hn : n = 2 ∨ n = 3) {o : Nat}
    (ho : o = oDig ∨ o = oLh) :
    RelCT isa (Two (LWT G f n)) (hashLabelT f o) fun _ _ => True := by
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  unfold hashLabelT seqs seqs seqs seqs seqs
  refine RelCT.seq (two_pieceF (Ψ := fun q t => LWT G f n q t ∧ t.gpr .rdi = off q.S oSt) [] []
    (fun q => q.F) (fun q => q.ws) (fun _ _ => 0) (fun q t h => h.lw.fr) nopin (by decide)
    (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun q t h =>
      WP.mono (wp_gs (block_good _ rfl) (scr_ok h.lw.L (d := .rdi) (by decide) (o := oSt) (by decide)))
        fun t' ⟨⟨hdi, hm, k⟩, _, sy⟩ => ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm sy, hdi⟩) ?_
  refine RelCT.seq (two_post (Ψ := LWT G f n) (two_tcall 0 (fun q => q.F) (fun q => q.S) (fun q => q.ws)
      (fun q => q.p) (fun q => q.ai)
      (fun q t h => ⟨h.1.lw.fv, h.1.lw.L, h.1.w35, h.1.tabAt.rd 0 (by decide), h.1.tabAt.mem.1.trans h.1.ai,
        h.1.ai, h.1.tabAt.ok.i⟩) (tload_taint hn 0 (by decide))
      (two_init hG (fun q => q.F) (fun q => q.S) fun q t ⟨t₀, h, k, hm, _⟩ =>
        ⟨lay_keep11 h.1.lw.L k hm, (k.gpr (by decide)).trans h.2⟩))
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.1.lw.rep
    exact WP.mono (wp_gs (tcall_good hgi 0) (initT_ok hG h.1.lw.L R (h.1.w35' R) h.1.tabAt h.2))
      fun t' ⟨⟨L', rd', wr', _, R', _⟩, fr, sy⟩ => h.1.after L' rd' wr' R R' A fr sy
  refine RelCT.seq (two_pieceF (Ψ := fun q t => LWT G f n q t ∧ t.gpr .rdi = off q.S oSt ∧
      t.gpr .rsi = BitVec.ofNat 64 0 ∧ t.gpr .rdx = q.lab ∧ t.gpr .rcx = BitVec.ofNat 64 q.labLen ∧
      t.gpr .r8 = off q.S oW) [] [] (fun q => q.F) (fun q => q.ws) (fun _ _ => 0)
    (fun q t h => h.lw.fr) nopin (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.lw.rep
    exact WP.mono (wp_gs (block_good _ rfl) (labA_ok h.lw.L R A)) fun t' ⟨⟨hdi, hsi, hdx, hcx, h8, hm, k⟩, _, sy⟩ =>
      ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm sy, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := LWT G f n) (two_tcall 1 (fun q => q.F) (fun q => q.S) (fun q => q.ws)
      (fun q => q.p) (fun q => q.au)
      (fun q t h => ⟨h.1.lw.fv, h.1.lw.L, h.1.w35, h.1.tabAt.rd 1 (by decide), h.1.tabAt.mem.2.1.trans h.1.au,
        h.1.au, h.1.tabAt.ok.u⟩) (tload_taint hn 1 (by decide))
      (two_updExt hG (fun q => q.F) (fun q => q.S) (fun q => q.lab) (fun q => q.labLen)
        (fun _ => BitVec.ofNat 64 0) fun q t ⟨t₀, h, k, hm, _⟩ => by
          obtain ⟨V, W, R, A⟩ := h.1.lw.rep
          exact ⟨lay_keep11 h.1.lw.L k hm, A.len, by rw [k.2.1, k.2.2]; exact A.cov, A.dS, A.dK,
            (k.gpr (by decide)).trans h.2.1, (k.gpr (by decide)).trans h.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.2.2⟩))
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.1.lw.rep
    exact WP.mono (wp_gs (tcall_good hgu 1) (updExtT_ok hG h.1.lw.L R (h.1.w35' R) h.1.tabAt A.len A.cov A.dS A.dK
      h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2))
      fun t' ⟨⟨L', rd', wr', _, R', _⟩, fr, sy⟩ => h.1.after L' rd' wr' R R' A fr sy
  refine RelCT.seq (two_pieceF (Ψ := fun q t => LWT G f n q t ∧ t.gpr .rdi = off q.S oSt ∧
      t.gpr .rsi = BitVec.ofNat 64 q.labLen ∧ t.gpr .rdx = off q.S o ∧ t.gpr .rcx = off q.S oW) [] []
    (fun q => q.F) (fun q => q.ws) (fun _ _ => 0) (fun q t h => h.lw.fr) nopin (by decide)
    (by rcases ho with rfl | rfl <;> rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.lw.rep
    exact WP.mono (wp_gs (block_good _ rfl) (labF_ok h.lw.L R A.hll (o := o) (by rcases ho with rfl | rfl <;> decide)))
      fun t' ⟨⟨hdi, hsi, hdx, hcx, hm, k⟩, _, sy⟩ => ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm sy, hdi, hsi, hdx, hcx⟩
  exact two_tcall 2 (fun q => q.F) (fun q => q.S) (fun q => q.ws) (fun q => q.p) (fun q => q.af)
    (fun q t h => ⟨h.1.lw.fv, h.1.lw.L, h.1.w35, h.1.tabAt.rd 2 (by decide), h.1.tabAt.mem.2.2.trans h.1.af,
      h.1.af, h.1.tabAt.ok.f⟩) (tload_taint hn 2 (by decide))
    (two_fin hG (fun q => q.F) (fun q => q.S) (fun _ => o) (fun q => BitVec.ofNat 64 q.labLen)
      fun q t ⟨t₀, h, k, hm, _⟩ => ⟨lay_keep11 h.1.lw.L k hm, Or.inr hoo, (k.gpr (by decide)).trans h.2.1,
        (k.gpr (by decide)).trans h.2.2.1, (k.gpr (by decide)).trans h.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2⟩)

/-! ## The branch on the digest length -/

/-- After a comparison, from a point of `Φ`: the flags but for which nothing
changed. -/
def AfterCmp {α : Type} (Φ : α → State → Prop) (a : α) (t : State) : Prop :=
  ∃ t₀, Φ a t₀ ∧ Keep [] t₀ t ∧ t.mem = t₀.mem ∧ t.syms = t₀.syms ∧ t.mxcsr = t₀.mxcsr

/-- `byLen` in two runs with the same digest length `D a` in `r11`: both take
the branch of `D a`. -/
theorem byLen_ct {α : Type} {b : Nat → Prog isa} {Q : State → State → Prop} (D : α → Nat) :
    ∀ {ds : List Nat} {Φ : α → State → Prop}, (∀ x ∈ ds, x < 2 ^ 31 ∧
      ∃ hc, (taint.check (Taint.ofRegs []) (.block [.alu .cmp .r11 (im x)]) hc).isSome = true) →
    (∀ a t, Φ a t → t.gpr .r11 = BitVec.ofNat 64 (D a) ∧ D a ∈ ds ∧ D a < 2 ^ 31) →
    (∀ d ∈ ds, RelCT isa (Two fun a t => AfterCmp Φ a t ∧ D a = d) (b d) Q) →
    RelCT isa (Two Φ) (byLen b ds) Q
  | [], _, _, hv, _ => RelCT.of_false fun s₁ _ ⟨a, h₁, _⟩ => absurd (hv a s₁ h₁).2.1 List.not_mem_nil
  | [x], _, _, hv, hb => (hb x (List.mem_singleton_self _)).mono (fun _ _ ⟨a, h₁, h₂⟩ =>
      ⟨a, ⟨⟨_, h₁, ⟨fun _ _ => rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, List.mem_singleton.mp (hv a _ h₁).2.1⟩,
        ⟨⟨_, h₂, ⟨fun _ _ => rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, List.mem_singleton.mp (hv a _ h₂).2.1⟩⟩)
      fun _ _ h => h
  | x :: y :: ds, Φ, hx, hv, hb => by
    obtain ⟨hx0, htx⟩ := hx x (List.mem_cons_self ..)
    obtain ⟨hc, htx⟩ := htx
    refine RelCT.seq (two_post (Ψ := fun a t => AfterCmp Φ a t ∧ t.zf = some (decide (D a = x)))
      (two_taint [] (fun _ _ _ _ _ r hr => absurd hr List.not_mem_nil) htx) fun a t h => ?_) ?_
    · obtain ⟨h11, -, hd⟩ := hv a t h
      exact WP.mono (cmpLen_ok h11 hd hx0) fun t' ⟨hz, k, hm, hs, hmx⟩ => ⟨⟨t, h, k, hm, hs, hmx⟩, hz⟩
    refine two_ite (fun a s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
    · refine (hb x (List.mem_cons_self ..)).mono (fun _ _ ⟨a, ⟨⟨c₁, z₁⟩, e₁⟩, ⟨⟨c₂, _⟩, _⟩⟩ => ?_) fun _ _ h => h
      have hDx : D a = x := by
        simpa only [eval, z₁, Option.some.injEq, decide_eq_true_eq] using e₁
      exact ⟨a, ⟨c₁, hDx⟩, ⟨c₂, hDx⟩⟩
    · refine byLen_ct D (Φ := fun a t => (AfterCmp Φ a t ∧ t.zf = some (decide (D a = x))) ∧
          isa.eval .e t = some false) (fun z hz => hx z (List.mem_cons_of_mem _ hz))
        (fun a t ⟨⟨⟨t₀, h₀, k, _⟩, z⟩, e⟩ => ?_) (fun d hd => (hb d (List.mem_cons_of_mem _ hd)).mono
          (fun _ _ ⟨a, ⟨⟨t₁, ⟨⟨⟨u₁, h₁, k₁, m₁, s₁, x₁⟩, _⟩, _⟩, k₁', m₁', s₁', x₁'⟩, d₁⟩,
            ⟨⟨t₂, ⟨⟨⟨u₂, h₂, k₂, m₂, s₂, x₂⟩, _⟩, _⟩, k₂', m₂', s₂', x₂'⟩, d₂⟩⟩ =>
            ⟨a, ⟨⟨u₁, h₁, ⟨fun _ hr => (k₁'.gpr hr).trans (k₁.gpr hr), k₁'.2.1.trans k₁.2.1, k₁'.2.2.trans k₁.2.2⟩,
                m₁'.trans m₁, s₁'.trans s₁, x₁'.trans x₁⟩, d₁⟩,
              ⟨⟨u₂, h₂, ⟨fun _ hr => (k₂'.gpr hr).trans (k₂.gpr hr), k₂'.2.1.trans k₂.2.1, k₂'.2.2.trans k₂.2.2⟩,
                m₂'.trans m₂, s₂'.trans s₂, x₂'.trans x₂⟩, d₂⟩⟩) fun _ _ h => h)
      obtain ⟨h11, hm, hd⟩ := hv a t₀ h₀
      have hne : D a ≠ x := by
        simpa only [eval, z, Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_false_iff_not] using e
      exact ⟨(k.gpr (by simp)).trans h11, (List.mem_cons.mp hm).resolve_left hne, hd⟩

theorem cmpLens_taint : ∀ x ∈ lens, x < 2 ^ 31 ∧
    ∃ hc, (taint.check (Taint.ofRegs []) (.block [.alu .cmp .r11 (im x)]) hc).isSome = true := by
  intro x hx
  simp only [lens, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, _, by taint_decide⟩

end VG.Proof.RsaOaep.X86_64
