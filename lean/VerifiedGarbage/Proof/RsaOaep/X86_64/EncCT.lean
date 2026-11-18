module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCorrect
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Spec.RsaPkcs1Sig
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCorrect
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
meta import VerifiedGarbage.Spec.RsaPkcs1Sig
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCall
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCall
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncMain
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
public import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncEm
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncMain
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncEm
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `RsaOaep.X86_64.LabelTCT`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.X86_64.MgfTCT`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP on x86-64: MGF1 with the hash function of a table, in constant time

`Table.mgfXor lay f` is constant time in two runs with the same frame,
regions, `src` and `dst`, the same table (its address in the slot `sTab`)
and the hash function's functions at the same addresses (`MQT`), whatever
the bytes they hold (`mgfT_ct`): each indirect call is to the same address
in both runs, and so of the same function (`two_tcall`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Table

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64.Table (Fns tcall tabArg tabHead)
open VG.Impl.Mgf1.X86_64 (sp at_ seqs initArgs updSrcArgs updCtrArgs finArgs)
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifn)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post two_map two_loop)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

/-! ## An indirect call in two runs -/

/-- An indirect call of the table's function `j` in two runs whose table
(word 35) and functions' addresses agree: of the same function in both,
whose call is constant time from what the load of its address keeps. -/
theorem two_tcall {α : Type} {Φ : α → State → Prop} {k : Nat} (j : Nat) {ts : List (String × Prog isa)}
    {n : String} {c : Prog isa} (F S : α → Addr) (ws : α → List Region) (p addr : α → Addr)
    (hv : ∀ a t, Φ a t → FrV k (F a) (ws a) t ∧ Lay t (F a) (S a) ∧ word t.mem (F a) (8 * 35) = p a ∧
      InRegions (t.rd ++ t.wr) (off (p a) (8 * j)) 8 ∧ t.mem.readW (off (p a) (8 * j)) 64 = addr a ∧
      t.syms n = addr a ∧ ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c))
    (htaint : ∃ hc, (taint.check (frT [] [35] k)
      (.block [.mov .r11 (.mem (sp sTab)), .mov .r11 (.mem (at_ .r11 (8 * j)))]) hc).isSome = true)
    (hcall : RelCT isa (Two fun a t => ∃ t₀, Φ a t₀ ∧ Keep [.r11] t₀ t ∧ t.mem = t₀.mem ∧ t.syms = t₀.syms)
      (.call n c) fun _ _ => True) :
    RelCT isa (Two Φ) (tcall sTab j ts) fun _ _ => True := by
  unfold tcall
  refine RelCT.seq (two_pieceF (Ψ := fun a t => (∃ t₀, Φ a t₀ ∧ Keep [.r11] t₀ t ∧ t.mem = t₀.mem ∧
      t.syms = t₀.syms) ∧ t.gpr .r11 = addr a ∧ ts.find? (fun q => t.syms q.1 == addr a) = some (n, c))
    [] [35] F ws (fun a _ => p a)
    (fun a t h => ⟨(hv a t h).1, fun k hk => by
      simp only [List.mem_singleton] at hk; subst hk; exact (hv a t h).2.2.1⟩) nopin (by decide) htaint
    fun a t h => ?_) ?_
  · obtain ⟨-, L, w35, hrd, hw, hn, hf⟩ := hv a t h
    have w35' : t.mem.readW (off (F a) sTab) 64 = p a := w35
    refine WP.mono (WP.keep [.r11] (Q := fun t' => t'.gpr .r11 = addr a ∧ t'.mem = t.mem ∧ t'.syms = t.syms)
      ?_ rfl) fun t' ⟨⟨h11, hm, hs⟩, kk⟩ => ⟨⟨t, h, kk, hm, hs⟩, h11, by rw [hs, ← hn]; exact hf⟩
    xrun [ea_sp, VG.Proof.RsaOaep.X86_64.ea_at, L.rsp, L.ld (d := sTab) (by decide), w35', hrd, hw, setReg_syms]
  · cases ts with
    | nil =>
      exact RelCT.of_false fun s₁ s₂ ⟨a, h₁, _⟩ => by simp at h₁
    | cons q ts =>
      exact RelCT.icalls_of_call (hcall.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)
        fun s₁ s₂ ⟨a, h₁, h₂⟩ => ⟨addr a, by simp only [icall, h₁.2.1], by simp only [icall, h₂.2.1],
          h₁.2.2, h₂.2.2, rfl⟩

/-! ## The points of a round -/

/-- MGF1's public data with a table: `MQ`, the table's address, and the
addresses of the hash function's `init`, `update` and `finalize`. -/
structure MQT extends MQ where
  p : Addr
  ai : Addr
  au : Addr
  af : Addr

/-- The frame's words MGF1 reads, with the counter `c`. -/
def mwT (D : Nat) (q : MQT) (c k : Nat) : BitVec 64 :=
  if k = 35 then q.p else if k = 36 then BitVec.ofNat 64 D else mw D q.toMQ c k

/-- A point of the round with counter `c`: `RW`, the table's slots, the
table, and the functions' addresses. -/
structure RWT (G : Stream) (f : Fns) (n : Nat) (q : MQT) (c : Nat) (t : State) : Prop where
  rw : RW n G.D q.toMQ c t
  w35 : word t.mem q.F (8 * 35) = q.p
  w36 : word t.mem q.F (8 * 36) = BitVec.ofNat 64 G.D
  tab : ∃ u₀ sArg, Tab G f q.F q.p sArg u₀ ∧ TJ u₀ q.F t ∧ t.rd = u₀.rd ∧ t.wr = u₀.wr
  ai : t.syms G.initN = q.ai
  au : t.syms G.updN = q.au
  af : t.syms G.finN = q.af

variable {G : Stream} {f : Fns} {n : Nat}

theorem mwT_old {D : Nat} {q : MQT} {c k : Nat} (h₁ : k ≠ 35) (h₂ : k ≠ 36) : mwT D q c k = mw D q.toMQ c k := by
  simp only [mwT, h₁, h₂, ite_false]

theorem RWT.words {q : MQT} {c : Nat} {t : State} (h : RWT G f n q c t) {ks : List Nat}
    (hks : ∀ k ∈ ks, k ∈ [14, 15, 16, 17, 18, 19, 20, 35, 36]) :
    FrV n q.F q.ws t ∧ ∀ k ∈ ks, word t.mem q.F (8 * k) = mwT G.D q c k := by
  refine ⟨h.rw.fv, fun k hk => ?_⟩
  have := hks k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [mwT_old (by decide) (by decide)]; exact h.rw.words.2 _ (by decide)
  · rw [mwT_old (by decide) (by decide)]; exact h.rw.words.2 _ (by decide)
  · rw [mwT_old (by decide) (by decide)]; exact h.rw.words.2 _ (by decide)
  · rw [mwT_old (by decide) (by decide)]; exact h.rw.words.2 _ (by decide)
  · rw [mwT_old (by decide) (by decide)]; exact h.rw.words.2 _ (by decide)
  · rw [mwT_old (by decide) (by decide)]; exact h.rw.words.2 _ (by decide)
  · rw [mwT_old (by decide) (by decide)]; exact h.rw.words.2 _ (by decide)
  · exact h.w35
  · exact h.w36

theorem RWT.tabAt {q : MQT} {c : Nat} {t : State} (h : RWT G f n q c t) : TabAt G f q.p t := by
  obtain ⟨u₀, _, T, J, rd, wr⟩ := h.tab
  exact T.at J rd wr

theorem TJ.ofMem {u₀ v v' : State} {F : Addr} (J : TJ u₀ F v) (hm : v'.mem = v.mem) (hs : v'.syms = v.syms) :
    TJ u₀ F v' :=
  ⟨by rw [hm]; exact J.fr, hs.trans J.sy⟩

theorem RWT.congr {q : MQT} {c : Nat} {t t' : State} (h : RWT G f n q c t) (hsp : t'.gpr .rsp = t.gpr .rsp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem) (hs : t'.syms = t.syms) :
    RWT G f n q c t' := by
  obtain ⟨u₀, sA, T, J, rd, wr⟩ := h.tab
  exact ⟨h.rw.congr hsp hwr hm, by rw [hm]; exact h.w35, by rw [hm]; exact h.w36,
    ⟨u₀, sA, T, J.ofMem hm hs, hrd.trans rd, hwr.trans wr⟩, by rw [hs]; exact h.ai, by rw [hs]; exact h.au,
    by rw [hs]; exact h.af⟩

/-- After a piece that keeps the regions, with the slots as they were. -/
theorem RWT.after {q : MQT} {c : Nat} {t t' : State} (h : RWT G f n q c t) (L' : Lay t' q.F q.S)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) {V V' : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem q.F q.S V W) (R' : Rep t'.mem q.F q.S V' W)
    (A : MArgs W q.S q.src q.srcLen q.dst q.dstLen) (h19 : W 19 = BitVec.ofNat 64 c)
    (h20 : W 20 = BitVec.ofNat 64 (c * G.D)) (hf : Frame (t.wr ++ [below (t.gpr .rsp) 16]) t.mem t'.mem)
    (hs : t'.syms = t.syms) : RWT G f n q c t' := by
  obtain ⟨u₀, sA, T, J, rd, wr⟩ := h.tab
  exact ⟨h.rw.after L' hwr R' A h19 h20, by rw [R'.fr 35 (by decide), ← R.fr 35 (by decide)]; exact h.w35,
    by rw [R'.fr 36 (by decide), ← R.fr 36 (by decide)]; exact h.w36,
    ⟨u₀, sA, T, J.step wr h.rw.L.rsp hf hs, hrd.trans rd, hwr.trans wr⟩, by rw [hs]; exact h.ai,
    by rw [hs]; exact h.au, by rw [hs]; exact h.af⟩

theorem RWT.w35' {q : MQT} {c : Nat} {t : State} (h : RWT G f n q c t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem q.F q.S V W) : W 35 = q.p := (R.fr 35 (by decide)).symm.trans h.w35

theorem RWT.w36' {q : MQT} {c : Nat} {t : State} (h : RWT G f n q c t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem q.F q.S V W) : W 36 = BitVec.ofNat 64 G.D := (R.fr 36 (by decide)).symm.trans h.w36

variable (G f n)

abbrev P0T (a : MQT × Nat) (t : State) : Prop := RWT G f n a.1 a.2 t

abbrev P1T (a : MQT × Nat) (t : State) : Prop := RWT G f n a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt

abbrev P3T (a : MQT × Nat) (t : State) : Prop :=
  RWT G f n a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 0 ∧
    t.gpr .rdx = off a.1.S a.1.src ∧ t.gpr .rcx = BitVec.ofNat 64 a.1.srcLen ∧ t.gpr .r8 = off a.1.S oW

abbrev P5T (a : MQT × Nat) (t : State) : Prop :=
  RWT G f n a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 a.1.srcLen ∧
    t.gpr .rdx = off a.1.S oCtr ∧ t.gpr .rcx = BitVec.ofNat 64 4 ∧ t.gpr .r8 = off a.1.S oW

abbrev P7T (a : MQT × Nat) (t : State) : Prop :=
  RWT G f n a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 (a.1.srcLen + 4) ∧
    t.gpr .rdx = off a.1.S oDig ∧ t.gpr .rcx = off a.1.S oW

variable {G f n}

theorem tload_taint (hn : n = 2 ∨ n = 3) (j : Nat) (hj : j = 0 ∨ j = 1 ∨ j = 2) :
    ∃ hc, (taint.check (frT [] [35] n)
      (.block [.mov .r11 (.mem (sp sTab)), .mov .r11 (.mem (at_ .r11 (8 * j)))]) hc).isSome = true := by
  rcases hn with rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

variable (hG : StreamOK G)

include hG in
theorem roundT_ct (hn : n = 2 ∨ n = 3) (hgi : FnsGood f.init) (hgu : FnsGood f.upd) (hgf : FnsGood f.fin) :
    RelCT isa (Two (P0T G f n)) (Impl.Mgf1.X86_64.Table.round lay sTab sD f) fun _ _ => True := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have c1 : oSt = 3072 := rfl
  have c2 : oDig = 3328 := rfl
  have c3 : oCtr = 3456 := rfl
  have c4 : oW = 4096 := rfl
  have c5 : oRsa = 8192 := rfl
  unfold Impl.Mgf1.X86_64.Table.round seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine RelCT.seq (two_pieceF (Ψ := P1T G f n) [] [] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mwT G.D a.1 a.2) (fun a t h => h.words (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
    fun a t h => WP.mono (wp_gs (block_good _ rfl) (scr_ok h.rw.L (d := .rdi) (by decide) (o := oSt) (by decide)))
      fun t' ⟨⟨hdi, hm, k⟩, _, sy⟩ => ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm sy, hdi⟩) ?_
  refine RelCT.seq (two_post (Ψ := P0T G f n) (two_tcall 0 (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws)
      (fun a => a.1.p) (fun a => a.1.ai)
      (fun a t h => ⟨h.1.rw.fv, h.1.rw.L, h.1.w35, h.1.tabAt.rd 0 (by decide), h.1.tabAt.mem.1.trans h.1.ai,
        h.1.ai, h.1.tabAt.ok.i⟩) (tload_taint hn 0 (by decide))
      (two_init hG (fun a => a.1.F) (fun a => a.1.S) fun a t ⟨t₀, h, k, hm, _⟩ =>
        ⟨lay_keep11 h.1.rw.L k hm, (k.gpr (by decide)).trans h.2⟩))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.1.rw.rep
    exact WP.mono (wp_gs (tcall_good hgi 0) (initT_ok hG h.1.rw.L R (h.1.w35' R) h.1.tabAt h.2))
      fun t' ⟨⟨L', rd', wr', _, R', _⟩, fr, sy⟩ => h.1.after L' rd' wr' R R' A h19 h20 fr sy
  -- `update` with `src`.
  refine RelCT.seq (two_pieceF (Ψ := P3T G f n) [] [] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mwT G.D a.1 a.2) (fun a t h => h.words (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.rw.rep
    exact WP.mono (wp_gs (block_good _ rfl) (updSrc_ok h.rw.L R A)) fun t' ⟨⟨hdi, hsi, hdx, hcx, h8, hm, k⟩, _, sy⟩ =>
      ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm sy, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := P0T G f n) (two_tcall 1 (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws)
      (fun a => a.1.p) (fun a => a.1.au)
      (fun a t h => ⟨h.1.rw.fv, h.1.rw.L, h.1.w35, h.1.tabAt.rd 1 (by decide), h.1.tabAt.mem.2.1.trans h.1.au,
        h.1.au, h.1.tabAt.ok.u⟩) (tload_taint hn 1 (by decide))
      (two_upd hG (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.src) (fun a => a.1.srcLen)
        (fun _ => BitVec.ofNat 64 0) fun a t ⟨t₀, h, k, hm, _⟩ => by
          have := h.1.rw.fit.fs
          exact ⟨lay_keep11 h.1.rw.L k hm, by omega_using [c1, c5, this], by omega_using [this], by omega_using [c1, c4, this], (k.gpr (by decide)).trans h.2.1,
            (k.gpr (by decide)).trans h.2.2.1, (k.gpr (by decide)).trans h.2.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2.2⟩))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.1.rw.rep
    have := h.1.rw.fit.fs
    exact WP.mono (wp_gs (tcall_good hgu 1) (updT_ok hG h.1.rw.L R (h.1.w35' R) h.1.tabAt (a := a.1.src)
      (len := a.1.srcLen) (by omega_using [c1, c5, this]) (by omega_using [this]) (by omega_using [c1, c4, this]) h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2))
      fun t' ⟨⟨L', rd', wr', _, R', _⟩, fr, sy⟩ => h.1.after L' rd' wr' R R' A h19 h20 fr sy
  -- The counter, and `update` with it.
  refine RelCT.seq (two_pieceF (Ψ := P5T G f n) [] [14] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mwT G.D a.1 a.2) (fun a t h => h.words (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.rw.rep
    have := h.rw.lt
    have := h.rw.fit.dstB
    have hc : a.2 ≤ a.2 * G.D := Nat.le_mul_of_pos_right _ hzD
    exact WP.mono (wp_gs (block_good _ rfl) (updCtr_ok h.rw.L R A.hsl h19 (by omega_arith)))
      fun t' ⟨⟨L', hdi, hsi, hdx, hcx, h8, k, R'⟩, fr, sy⟩ =>
        ⟨h.after L' k.2.1 k.2.2 R R' A h19 h20 fr sy, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := P0T G f n) (two_tcall 1 (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws)
      (fun a => a.1.p) (fun a => a.1.au)
      (fun a t h => ⟨h.1.rw.fv, h.1.rw.L, h.1.w35, h.1.tabAt.rd 1 (by decide), h.1.tabAt.mem.2.1.trans h.1.au,
        h.1.au, h.1.tabAt.ok.u⟩) (tload_taint hn 1 (by decide))
      (two_upd hG (fun a => a.1.F) (fun a => a.1.S) (fun _ => oCtr) (fun _ => 4)
        (fun a => BitVec.ofNat 64 a.1.srcLen) fun a t ⟨t₀, h, k, hm, _⟩ =>
          ⟨lay_keep11 h.1.rw.L k hm, by omega_using [c3, c5], by omega_using [hzS, c1, c3], by omega_using [c3, c4], (k.gpr (by decide)).trans h.2.1,
            (k.gpr (by decide)).trans h.2.2.1, (k.gpr (by decide)).trans h.2.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2.2⟩))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.1.rw.rep
    exact WP.mono (wp_gs (tcall_good hgu 1) (updT_ok hG h.1.rw.L R (h.1.w35' R) h.1.tabAt (a := oCtr) (len := 4)
      (by omega_using [c3, c5]) (by omega_using [hzS, c1, c3]) (by omega_using [c3, c4]) h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2))
      fun t' ⟨⟨L', rd', wr', _, R', _⟩, fr, sy⟩ => h.1.after L' rd' wr' R R' A h19 h20 fr sy
  -- `finalize`.
  refine RelCT.seq (two_pieceF (Ψ := P7T G f n) [] [] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mwT G.D a.1 a.2) (fun a t h => h.words (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.rw.rep
    exact WP.mono (wp_gs (block_good _ rfl) (finA_ok h.rw.L R A.hsl)) fun t' ⟨⟨hdi, hsi, hdx, hcx, hm, k⟩, _, sy⟩ =>
      ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm sy, hdi, hsi, hdx, hcx⟩
  refine RelCT.seq (two_post (Ψ := P0T G f n) (two_tcall 2 (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws)
      (fun a => a.1.p) (fun a => a.1.af)
      (fun a t h => ⟨h.1.rw.fv, h.1.rw.L, h.1.w35, h.1.tabAt.rd 2 (by decide), h.1.tabAt.mem.2.2.trans h.1.af,
        h.1.af, h.1.tabAt.ok.f⟩) (tload_taint hn 2 (by decide))
      (two_fin hG (fun a => a.1.F) (fun a => a.1.S) (fun _ => oDig)
        (fun a => BitVec.ofNat 64 (a.1.srcLen + 4)) fun a t ⟨t₀, h, k, hm, _⟩ =>
          ⟨lay_keep11 h.1.rw.L k hm, by omega_using [c1, c2, c4], (k.gpr (by decide)).trans h.2.1, (k.gpr (by decide)).trans h.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2⟩))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.1.rw.rep
    exact WP.mono (wp_gs (tcall_good hgf 2) (finT_ok hG h.1.rw.L R (h.1.w35' R) h.1.tabAt (o := oDig) (by omega_using [c1, c2, c4])
      h.2.1 h.2.2.2.1 h.2.2.2.2)) fun t' ⟨⟨L', rd', wr', _, R', _⟩, fr, sy⟩ => h.1.after L' rd' wr' R R' A h19 h20 fr sy
  -- Into `dst`, and the next counter.
  refine RelCT.seq (two_pieceF (Ψ := P0T G f n) [] [14, 17, 18, 20, 36] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mwT G.D a.1 a.2) (fun a t h => h.words (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.rw.rep
    have := h.rw.fit.fd
    exact WP.mono (wp_gs xorOutT_good (xorOutT_ok (G := G) h.rw.L R (dst := a.1.dst) (dstLen := a.1.dstLen)
        (done := a.2 * G.D) (by omega_using [this]) hzD (by omega_using [hzF, hzDF]) (h.w36' R) A.hdst A.hdl h20 h.rw.lt))
      fun t' ⟨⟨L', k, R'⟩, fr, sy⟩ => h.after L' k.2.1 k.2.2 R R' A h19 h20 fr sy
  exact two_taintF [] [] (fun a => a.1.F) (fun a => a.1.ws) (fun a => mwT G.D a.1 a.2)
    (fun a t h => h.words (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩)

/-! ## MGF1 -/

variable (G f n)

/-- Where MGF1 starts: in the frame, with its slots set, the table at the
word at `F + sArg`, and the functions' addresses. -/
structure MET (sArg : Nat) (q : MQT) (t : State) : Prop where
  me : ME n q.toMQ t
  tab : Tab G f q.F q.p sArg t
  ai : t.syms G.initN = q.ai
  au : t.syms G.updN = q.au
  af : t.syms G.finN = q.af

/-- After the table's address to its slot. -/
def MEA (sArg : Nat) (q : MQT) (t : State) : Prop :=
  FrV n q.F q.ws t ∧ Lay t q.F q.S ∧ MFit q.src q.srcLen q.dst q.dstLen ∧ ∃ t₀ V W,
    Tab G f q.F q.p sArg t₀ ∧ TJ t₀ q.F t ∧ Keep [.rax] t₀ t ∧ Rep t.mem q.F q.S V (upd W 35 q.p) ∧
    Rep t₀.mem q.F q.S V W ∧ MArgs W q.S q.src q.srcLen q.dst q.dstLen ∧
    t₀.syms G.initN = q.ai ∧ t₀.syms G.updN = q.au ∧ t₀.syms G.finN = q.af

/-- Before the round with counter `j`. -/
def MLT (Gs : Spec.Mgf1.Hash) (q : MQT) (j : Nat) (t : State) : Prop :=
  FrV n q.F q.ws t ∧ MFit q.src q.srcLen q.dst q.dstLen ∧ ∃ u₀ sArg V W, MArgs W q.S q.src q.srcLen q.dst q.dstLen ∧
    MgfI u₀ q.F q.S V W (Spec.Mgf1.mgf1 Gs (srcB V q.src q.srcLen) q.dstLen) q.dst q.dstLen G.D j t ∧
    TJ u₀ q.F t ∧ Tab G f q.F q.p sArg u₀ ∧ W 35 = q.p ∧ W 36 = BitVec.ofNat 64 G.D ∧
    u₀.syms G.initN = q.ai ∧ u₀.syms G.updN = q.au ∧ u₀.syms G.finN = q.af

variable {G f n}

include hG in
theorem MLT.rwt {Gs : Spec.Mgf1.Hash} {q : MQT} {j : Nat} {t : State} (h : MLT G f n Gs q j t)
    (hj : j < nR G.D q.toMQ) : RWT G f n q j t := by
  obtain ⟨fv, fit, u₀, sA, V, W, A, I, J, T, h35, h36, hi, hu, hf⟩ := h
  obtain ⟨V', W', R', h19, h20, hW, -⟩ := I.rep
  exact ⟨⟨fv, I.L, fit, (lt_nR (sizes hG).2.2.2.2 q.toMQ j).mp hj, V', W', R',
      A.of_eq fun k h1 h2 => hW k (by unfold nW frameBytes; omega_using [h2]) (by omega_using [h2]) (by omega_using [h2]), h19, h20⟩,
    by rw [R'.fr 35 (by decide), hW 35 (by decide) (by decide) (by decide), h35],
    by rw [R'.fr 36 (by decide), hW 36 (by decide) (by decide) (by decide), h36],
    ⟨u₀, sA, T, J, I.rd, I.wr⟩, by rw [J.sy, hi], by rw [J.sy, hu], by rw [J.sy, hf]⟩

include hG in
/-- `dst ⊕= MGF1(src, dstLen)`, with the hash function of the table at
`[rsp + sArg]`, in two runs with the same `MQT`. -/
theorem mgfT_ct (hgi : FnsGood f.init) (hgu : FnsGood f.upd) (hgf : FnsGood f.fin)
    {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) (hn : n = 2 ∨ n = 3) {sArg : Nat}
    (htA : ∃ hc, (taint.check (frT [] [] n) (.block (tabArg sArg sTab)) hc).isSome = true) :
    RelCT isa (Two (MET G f n sArg)) (Impl.Mgf1.X86_64.Table.mgfXor lay sArg sTab sD f) fun _ _ => True := by
  have hD := (sizes hG).2.2.2.2
  unfold Impl.Mgf1.X86_64.Table.mgfXor seqs seqs
  -- The table's address.
  refine RelCT.seq (two_pieceF (Ψ := MEA G f n sArg) [] [] (fun q => q.F) (fun q => q.ws) (fun _ _ => 0)
    (fun q t h => ⟨h.me.fv, fun _ h => absurd h List.not_mem_nil⟩) nopin (by decide) htA fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A⟩ := h.me.rep
    exact WP.mono (wp_gs (block_good _ rfl) (tabArg_ok (G := G) h.me.L R h.tab))
      fun t' ⟨⟨k, L', R', _⟩, fr, sy⟩ => ⟨h.me.fv.congr (k.gpr (by decide)) k.2.2, L', h.me.fit, t, V, W, h.tab,
        (TJ.refl t q.F).step rfl h.me.L.rsp fr sy, k, R', R, A, h.ai, h.au, h.af⟩
  -- Its digest length, the counter and `done`.
  refine RelCT.seq (two_pieceF (Ψ := fun q t => 0 < nR G.D q.toMQ ∧ MLT G f n Gs q 0 t) [] [35] (fun q => q.F)
    (fun q => q.ws) (fun q _ => q.p)
    (fun q t h => ⟨h.1, fun k hk => by
      simp only [List.mem_singleton] at hk; subst hk
      obtain ⟨-, -, -, t₀, V, W, -, -, -, R', -⟩ := h
      rw [R'.fr 35 (by decide)]; simp [upd]⟩)
    nopin (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun q t h => ?_) ?_
  · obtain ⟨fv, L, fit, t₀, V, W, T, J, k, R', R, A, hi, hu, hf⟩ := h
    have hpos := fit.pos
    have hD' := (T.mem _ J.fr).2.1
    exact WP.mono (wp_gs (block_good _ rfl) (tabHead_ok (G := G) (p := q.p) L R' (by simp [upd])
        (by rw [k.2.1, k.2.2]; exact T.rdD) hD'
        (Spec.Mgf1.mgf1 Gs (srcB V q.src q.srcLen) q.dstLen) q.dst q.dstLen))
      fun v ⟨⟨I, _⟩, fr, sy⟩ => ⟨(lt_nR hD q.toMQ 0).mpr (by omega_using [hpos]), fv.congr (I.L.rsp.trans L.rsp.symm) I.wr,
        fit, t₀, sArg, V, upd (upd W 35 q.p) 36 (BitVec.ofNat 64 G.D),
        A.of_eq fun k h1 h2 => by simp only [upd]; rw [ifn (by omega_using [h2]), ifn (by omega_using [h2])],
        mgfI_rebase I k.2.1 k.2.2 (keep_cs' k (cs_disj _ (by decide))), J.step k.2.2 L.rsp fr sy, T,
        by simp [upd], by simp [upd], hi, hu, hf⟩
  refine (two_loop (Ψ := fun _ _ => True) (fun q => nR G.D q.toMQ)
    (two_map id (fun p s h => MLT.rwt hG h.2 h.1) (roundT_ct hG hn hgi hgu hgf)) fun q j t hj h => ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  obtain ⟨fv, fit, u₀, sA, V, W, A, I, J, T, h35, h36, hi, hu, hf⟩ := h
  refine WP.mono (roundT_ok hG hgi hgu hgf hGh hGl hGv T fit A h35 h36 I J ((lt_nR hD q.toMQ j).mp hj))
    fun t' ⟨hcf, I', J'⟩ => ?_
  have e : decide ((j + 1) * G.D < q.dstLen) = decide (j + 1 < nR G.D q.toMQ) := by
    rw [decide_eq_decide]; exact (lt_nR hD q.toMQ (j + 1)).symm
  refine ⟨by simp only [eval, hcf, e], fun _ => ⟨fv.congr (I'.L.rsp.trans I.L.rsp.symm) (I'.wr.trans I.wr.symm),
    fit, u₀, sA, V, W, A, I', J', T, h35, h36, hi, hu, hf⟩, fun _ => trivial⟩

end VG.Proof.RsaOaep.X86_64.Table

end

end

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

end

end

/-! ### `RsaOaep.X86_64.EncSteps`, which only this module used -/

section

/-!
# RSAES-OAEP encryption on x86-64: the points between the pieces

What the constant-time proof needs to know of one run between the pieces of
`encMain`: in the frame, with the argument slots as the prologue stored them
(`EW`), MGF1's slots too before MGF1 (`EWM`), and the arguments of
`vg_rsa_public_checked` before its call (`EWP`). Each piece's step is its
correctness lemma, of which only this is kept.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

/-- In the frame, with the argument slots as the prologue stored them. -/
structure EW (s t : State) : Prop where
  he : EnvE s t
  L : Lay t (fb s) (stackArg s 6)
  rep : ∃ V W, Rep t.mem (fb s) (stackArg s 6) V W ∧ ArgsW s W

/-- Before MGF1, with its slots set. -/
structure EWM (s t : State) (src srcLen dst dstLen : Nat) : Prop where
  he : EnvE s t
  L : Lay t (fb s) (stackArg s 6)
  rep : ∃ V W, Rep t.mem (fb s) (stackArg s 6) V W ∧ ArgsW s W ∧ MArgs W (stackArg s 6) src srcLen dst dstLen

/-- The words of `vg_rsa_public_checked`'s stack arguments. -/
def pw (s : State) : Nat → BitVec 64
  | 0 => off (stackArg s 6) oEm
  | 1 => s.gpr .rcx
  | 2 => off (stackArg s 6) oRsa
  | _ => stackArg s 7 - 1024

/-- Before the call of `vg_rsa_public_checked`, with its arguments. -/
structure EWP (s t : State) : Prop where
  he : EnvE s t
  L : Lay t (fb s) (stackArg s 6)
  w : ∀ i < 4, t.mem.readW (off (fb s) (8 * i)) 64 = pw s i
  rdi : t.gpr .rdi = s.gpr .rdi
  rsi : t.gpr .rsi = s.gpr .rcx
  rdx : t.gpr .rdx = s.gpr .rdx
  rcx : t.gpr .rcx = s.gpr .rcx
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = s.gpr .r9

/-- The argument slots. -/
def encKs : List Nat := [14, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

theorem encKs_lt : ∀ k ∈ encKs, k < nW := by decide

theorem encKs_iff {k : Nat} (h : k ∈ encKs) : k = 14 ∨ (21 ≤ k ∧ k ≤ 31) := by
  simp only [encKs, List.mem_cons, List.not_mem_nil, or_false] at h; omega_using [h]

section
variable {H : Spec.Mgf1.Hash} {s t : State} (hp : EPre H s)
include hp

/-- The frame and the other writable regions. -/
theorem EnvE.frv (he : EnvE s t) : FrV 2 (fb s) [outR s, scrR s] t where
  rsp := he.rsp
  wr := he.wr
  two := rfl
  pw := by
    refine .cons ?_ (.cons ?_ (.cons (fun _ h => absurd h List.not_mem_nil) .nil))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.d_stk_out.sub_left (frame_sub s)
      · exact hp.d_stk_scr.sub_left (frame_sub s)
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact hp.d_out_scr
  len r hr := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Nat.le_of_lt (BitVec.isLt _)
    · have := hp.wS; simp only [scrR]; omega_using [this]

omit hp in
theorem EW.words (h : EW s t) : ∀ k ∈ encKs, word t.mem (fb s) (8 * k) = encW s k := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  intro k hk
  rw [R.fr k (encKs_lt k hk)]
  exact hW k (encKs_iff hk)

end

/-! ## The steps -/

section
variable {Hs : Spec.Mgf1.Hash} {s : State} (hp : EPre Hs s)
include hp

omit hp in
theorem ew_clearEm {t : State} (h : EW s t) : WP isa clearEm t (EW s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  exact WP.mono (wp_good clearEm_good (clearEm_ok h.L R)) fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
    ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, W, R1, hW⟩

theorem ew_copySeed {Hm : Stream} (hl : Hs.len = Hm.D) (hD : 0 < Hm.D) (hD64 : Hm.D ≤ 64) {t : State}
    (h : EW s t) : WP isa (copySeed Hm) t (EW s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, w31⟩ := hW.w
  have hsl := hp.hsl; have hk2 := hp.k2; have wSd := hp.wSd
  have hc : ∀ i < Hm.D, (⟨stackArg s 4, Hs.len⟩ : Region).Contains (stackArg s 4 + BitVec.ofNat 64 i) 1 :=
    fun i hi => Offset.contains_base (stackArg s 4) (d := i) (n := 1) (k := Hs.len) (by omega_using [hl, hi]) (by omega_using [hD64, hi])
  exact WP.mono (wp_good (copySeed_good _) (copySeed_ok (H := Hm) h.L R w31 hD hD64
    (fun i hi => hp.rd_in h.he.rd (by simp [rdL]) (hc i hi))
    (fun i hi j hj => ne_of_disjoint hp.d_sd_scr (hc i hi) (Offset.contains_base _
      (by unfold oEm at *; omega_using [hD64, hsl, hj]) (by unfold oEm at *; omega_using [hD64, hj])))))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, W, R1, hW⟩

/-- The label, where `hashLabel` finds it. -/
theorem EW.lab {t : State} (h : EW s t) {W : Nat → BitVec 64} (hW : ArgsW s W) :
    LabAt t (fb s) (stackArg s 6) W (stackArg s 0) (stackArg s 1).toNat := by
  obtain ⟨-, -, -, -, -, -, -, w27, w28, -⟩ := hW.w
  have hsl := hp.hsl
  have sS : Region.Sub ⟨stackArg s 6, oRsa⟩ (scrR s) := Region.sub_prefix (by unfold oRsa; omega_using [hsl])
  exact ⟨w27, by rw [w28, BitVec.ofNat_toNat, BitVec.setWidth_eq], (stackArg s 1).isLt,
    Covers.left (by rw [h.he.rd]; exact (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp [rdL]).trans hp.hrd),
    hp.d_lb_scr.sub_right sS, hp.d_stk_lb.sub_left (ret_sub s)⟩

theorem ew_hashLabelT {Hm : Hash} (hH : HashOK Hm) (mH : MgfLink Hm hH) {f : Impl.Mgf1.X86_64.Table.Fns}
    (hgi : Table.FnsGood f.init) (hgu : Table.FnsGood f.upd) (hgf : Table.FnsGood f.fin) {t : State}
    (h : EW s t) (h35 : word t.mem (fb s) (8 * 35) = stackArg s 10)
    (T : Table.Tab Hm.stream f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t) :
    WP isa (hashLabelT f oDig) t (EW s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  exact WP.mono (wp_good (hashLabelT_good hgi hgu hgf oDig)
    (hashLabelT_ok hH.stream hgi hgu (Hs := mH.G) mH.hash T (Table.TJ.refl t _) rfl rfl h.L R
      ((R.fr 35 (by decide)).symm.trans h35) (h.lab hp hW) (Or.inl rfl)))
    fun t3 ⟨⟨L3, rd3, wr3, cs3, V3, R3, _, _⟩, sp3, mx3, f3⟩ =>
      ⟨h.he.step rd3 wr3 sp3 (fun r hr _ => cs3 r hr) mx3 f3, L3, V3, W, R3, hW⟩

omit hp in
theorem ew_copyLh {Hm : Stream} (hD : 0 < Hm.D) (hD64 : Hm.D ≤ 64) {t : State} (h : EW s t) :
    WP isa (copyLh Hm) t (EW s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  exact WP.mono (wp_good (copyLh_good _) (copyLh_ok (H := Hm) h.L R hD hD64))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, W, R1, hW⟩

theorem ew_putMsg {D : Nat} (hk : 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) {t : State} (h : EW s t) :
    WP isa putMsg t (EW s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  obtain ⟨-, -, -, w23, -, -, -, -, -, w29, w30, -⟩ := hW.w
  have hk2 := hp.k2; have hsl := hp.hsl; have wM := hp.wM
  have hmA : ∀ i < (stackArg s 3).toNat, (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Contains
      (stackArg s 2 + BitVec.ofNat 64 i) 1 := fun i hi => Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  exact WP.mono (wp_good putMsg_good (putMsg_ok h.L R (k := (s.gpr .rcx).toNat) (mLen := (stackArg s 3).toNat)
    (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [w30, BitVec.ofNat_toNat, BitVec.setWidth_eq]) w29
    (by omega_using [hk]) hk2 (fun i hi => hp.rd_in h.he.rd (by simp [rdL]) (hmA i hi))
    (fun i hi j hj => ne_of_disjoint hp.d_ms_scr (hmA i hi) (Offset.contains_base _ (by omega_using [hk, hsl, hj]) (by omega_using [hj])))))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, W, R1, hW⟩

omit hp in
theorem ew_dbArgs {Hm : Stream} (hD : Hm.D < 2 ^ 30) (hkD : Hm.D + 1 ≤ (s.gpr .rcx).toNat) {t : State}
    (h : EW s t) : WP isa (.block (dbArgs Hm)) t fun t' =>
      EWM s t' (oEm + 1) Hm.D (oEm + 1 + Hm.D) ((s.gpr .rcx).toNat - (Hm.D + 1)) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  obtain ⟨-, -, -, w23, -⟩ := hW.w
  exact WP.mono (wp_good (dbArgs_good _) (dbArgs_ok (H := Hm) h.L R
    (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hD hkD))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, _, R1,
        fun k hk => (mW_other (by omega_using [hk])).trans (hW k hk), mW_args _ _ _ _ _ _⟩

omit hp in
theorem ew_seedArgs {Hm : Stream} (hD : Hm.D < 2 ^ 30) (hkD : Hm.D + 1 ≤ (s.gpr .rcx).toNat) {t : State}
    (h : EW s t) : WP isa (.block (seedArgs Hm)) t fun t' =>
      EWM s t' (oEm + 1 + Hm.D) ((s.gpr .rcx).toNat - (Hm.D + 1)) (oEm + 1) Hm.D := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  obtain ⟨-, -, -, w23, -⟩ := hW.w
  exact WP.mono (wp_good (seedArgs_good _) (seedArgs_ok (H := Hm) h.L R
    (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hD hkD))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, _, R1,
        fun k hk => (mW_other (by omega_using [hk])).trans (hW k hk), mW_args _ _ _ _ _ _⟩

omit hp in
theorem ew_mgfT {Gm : Hash} (hG : HashOK Gm) (mG : MgfLink Gm hG) {f : Impl.Mgf1.X86_64.Table.Fns}
    (hgi : Table.FnsGood f.init) (hgu : Table.FnsGood f.upd) (hgf : Table.FnsGood f.fin)
    {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {t : State}
    (h : EWM s t src srcLen dst dstLen)
    (T : Table.Tab Gm.stream f (fb s) (stackArg s 11) (frameBytes + 8 + 8 * 11) t) :
    WP isa (mgfT f 11) t (EW s) := by
  obtain ⟨V, W, R, hW, A⟩ := h.rep
  exact WP.mono (wp_good (Table.mgfT_good hgi hgu hgf _) (Table.mgfXorT_ok hG.stream hgi hgu hgf mG.hash mG.len
    (valid_of_link hG mG) T h.L R hf A))
    fun t1 ⟨⟨L1, rd1, wr1, cs1, V1, W1, R1, hW1, _⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step rd1 wr1 sp1 (fun r hr _ => cs1 r hr) mx1 f1, L1, V1, W1, R1, fun k hk => by
        rw [hW1 k (by rcases hk with rfl | hk <;> unfold nW frameBytes <;> omega_arith) (by omega_using [hk]) (by omega_using [hk]) (by omega_using [hk])
          (by omega_using [hk])]
        exact hW k hk⟩

omit hp in
theorem ew_pubArgs {t : State} (h : EW s t) : WP isa (.block pubArgs) t (EWP s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  exact WP.mono (wp_good pubArgs_good (pubArgs_ok h.L R fun k h1 h2 => hW k (.inr ⟨h1, by omega_using [h2]⟩)))
    fun t1 ⟨⟨L1, k1, R1, hdi, hsi, hdx, hcx, h8, h9⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, fun i hi => by
        rw [R1.rd i rfl (by unfold nW frameBytes; omega_using [hi])]
        match i, hi with
        | 0, _ => simp [upd, pw]
        | 1, _ => simp [upd, pw]
        | 2, _ => simp [upd, pw]
        | 3, _ => simp [upd, pw], hdi, hsi, hdx, hcx, h8, h9⟩

end

end VG.Proof.RsaOaep.X86_64

end

end

/-!
# RSAES-OAEP encryption on x86-64: constant time

Each point of the code is described, in each run, by what correctness says of
it from that run's entry state, which has the same public data as an anchor
(`EAt`, as in `Proof/RsaPkcs1Sig/X86_64/SignCT.lean`). The pieces between the
calls are checked by the taint analysis from the frame's public slots
(`e_taintF`); the branches are on `k` and the message's length, which are
public; MGF1 and the label's hash (`hashLabel_ct`) are constant time for the
same public data in both runs; and the call of
`vg_rsa_public_checked` is constant time for its contract, whose public data
(its registers, its stack arguments, `n` and `e`) are the same in both runs.
The code with `hLen` as an immediate is checked for every `hLen` up to 64.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.RsaPkcs1Sig.X86_64 (pubChecked pubChk)

/-! ## The taint checks of the code with `hLen` as an immediate -/

theorem pro_taint : (taint.check (Taint.ofRegs [.rsp]) (.block encPrologue)
    (taint.hintOf (Taint.ofRegs [.rsp]) (.block encPrologue))).isSome = true := by
  taint_decide

theorem chkK_taint : ∀ d < 65, (taint.check (Taint.ofRegs [.rsp]) (.block (chkK (gD d)))
    (taint.hintOf (Taint.ofRegs [.rsp]) (.block (chkK (gD 0))))).isSome = true := by
  decide +kernel

theorem etabSlot_taint : ∃ hc, (taint.check (frT [] [] 2) (.block (tabSlot 10)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem elenLoad_taint : ∃ hc, (taint.check (frT [] [35] 2) (.block lenLoad) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chkMsg_taint : ∀ d < 65, (taint.check (Taint.ofRegs [.rsp]) (.block (chkMsg (gD d)))
    (taint.hintOf (Taint.ofRegs [.rsp]) (.block (chkMsg (gD 0))))).isSome = true := by
  decide +kernel

theorem copySeed_taint : ∀ d < 65, (taint.check (frT [] [14, 31] 2) (copySeed (gD d))
    (taint.hintOf (frT [] [14, 31] 2) (copySeed (gD 0)))).isSome = true := by
  decide +kernel

theorem copyLh_taint : ∀ d < 65, (taint.check (frT [] [14] 2) (copyLh (gD d))
    (taint.hintOf (frT [] [14] 2) (copyLh (gD 0)))).isSome = true := by
  decide +kernel

theorem dbArgs_taint : ∀ d < 65, (taint.check (frT [] [] 2) (.block (dbArgs (gD d)))
    (taint.hintOf (frT [] [] 2) (.block (dbArgs (gD 0))))).isSome = true := by
  decide +kernel

theorem seedArgs_taint : ∀ d < 65, (taint.check (frT [] [] 2) (.block (seedArgs (gD d)))
    (taint.hintOf (frT [] [] 2) (.block (seedArgs (gD 0))))).isSome = true := by
  decide +kernel

/-! ## Entry states and the anchor -/

section
variable (H G : Spec.Mgf1.Hash) (P : State → State → Prop)

/-- An entry state with the public data of the anchor `a`, and what `P`
relates them by: more public data, for a variant with more arguments
(`PcCT`). -/
def ESib (a s : State) : Prop := EPre H s ∧ (encK H G).pub a s ∧ P a s

/-- What `J` says of a run from an entry state with the anchor's public data. -/
def EAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, ESib H G P a s ∧ J s t

theorem encPub_refl (s : State) : (encK H G).pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

end

variable {H G : Spec.Mgf1.Hash} {P : State → State → Prop}

theorem ESib.gpr {a s : State} (h : ESib H G P a s) {r : Reg}
    (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r := (h.2.1.1 r hr).symm

theorem ESib.arg {a s : State} (h : ESib H G P a s) {i : Nat} (hi : i < 8) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.1.2.1) i (List.mem_range.mpr hi)).symm

theorem ESib.fb {a s : State} (h : ESib H G P a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _; rw [h.gpr (r := .rsp) (by decide)]

theorem ESib.out_eq {a s : State} (h : ESib H G P a s) : outR s = outR a := by
  unfold outR; rw [h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide)]

theorem ESib.scr_eq {a s : State} (h : ESib H G P a s) : scrR s = scrR a := by
  unfold scrR; rw [h.arg (i := 6) (by decide), h.arg (i := 7) (by decide)]

theorem ESib.k {a s : State} (h : ESib H G P a s) : (s.gpr .rcx).toNat = (a.gpr .rcx).toNat := by
  rw [h.gpr (r := .rcx) (by decide)]

theorem ESib.w_eq {a s : State} (h : ESib H G P a s) {k : Nat} (hk : k ∈ encKs) : encW s k = encW a k := by
  simp only [encKs, List.mem_cons, List.not_mem_nil, or_false] at hk
  have hW : ∀ x : State, ArgsW x (encW x) := fun _ _ _ => rfl
  obtain ⟨a14, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31⟩ := (hW a).w
  obtain ⟨s14, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31⟩ := (hW s).w
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [s14, a14, h.arg (by decide)]
  · rw [s21, a21, h.gpr (by decide)]
  · rw [s22, a22, h.gpr (by decide)]
  · rw [s23, a23, h.gpr (by decide)]
  · rw [s24, a24, h.gpr (by decide)]
  · rw [s25, a25, h.gpr (by decide)]
  · rw [s26, a26, h.arg (by decide)]
  · rw [s27, a27, h.arg (by decide)]
  · rw [s28, a28, h.arg (by decide)]
  · rw [s29, a29, h.arg (by decide)]
  · rw [s30, a30, h.arg (by decide)]
  · rw [s31, a31, h.arg (by decide)]

/-! ## The pieces -/

/-- Code the taint analysis checks from the frame's argument slots `ks`. -/
theorem e_taintF {J : State → State → Prop} (hJ : ∀ s t, EPre H s → J s t → EW s t)
    (rs : List Reg) (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ encKs) (hpin : Pins (EAt H G P J) rs) {c : Prog isa}
    (h : ∃ hc, (taint.check (frT rs ks 2) c hc).isSome = true) :
    RelCT isa (Two (EAt H G P J)) c fun _ _ => True :=
  two_taintF rs ks fb (fun a => [outR a, scrR a]) encW (fun a t ⟨s, S, j⟩ => by
      have e := hJ s t S.1 j
      rw [← S.fb, ← S.out_eq, ← S.scr_eq]
      exact ⟨e.he.frv S.1, fun k hk => (e.words k (hks k hk)).trans (S.w_eq (hks k hk))⟩)
    hpin (fun k hk => encKs_lt k (hks k hk)) h

/-- What correctness says after a piece, from what the entry state's
relation to the anchor says too. -/
theorem e_postS {J J' : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (EAt H G P J)) c fun _ _ => True)
    (hw : ∀ a s t, ESib H G P a s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (EAt H G P J)) c (Two (EAt H G P J')) :=
  two_post hct fun a t ⟨s, S, j⟩ => WP.mono (hw a s t S j) fun _ j' => ⟨s, S, j'⟩

/-- What correctness says after a piece. -/
theorem e_post {J J' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Two (EAt H G P J)) c fun _ _ => True)
    (hw : ∀ s t, EPre H s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (EAt H G P J)) c (Two (EAt H G P J')) :=
  two_post hct fun _ t ⟨s, S, j⟩ => WP.mono (hw s t S.1 j) fun _ j' => ⟨s, S, j'⟩

theorem e_pins_rsp {J : State → State → Prop} (hJ : ∀ s t, EPre H s → J s t → t.gpr .rsp = fb s) :
    Pins (EAt H G P J) [.rsp] :=
  fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ r hr => by
    rw [List.mem_singleton.mp hr, hJ _ _ S₁.1 j₁, hJ _ _ S₂.1 j₂, S₁.fb, S₂.fb]

/-- A branch on a condition that the entry state's public data fixes. -/
theorem e_ite {J : State → State → Prop} {cond : isa.Cond} {th el : Prog isa} {Q : State → State → Prop}
    (f : State → Option Bool) (hf : ∀ s t, J s t → isa.eval cond t = f s) (hs : ∀ a s, ESib H G P a s → f s = f a)
    (ht : RelCT isa (Two fun a t => EAt H G P J a t ∧ isa.eval cond t = some true) th Q)
    (he : RelCT isa (Two fun a t => EAt H G P J a t ∧ isa.eval cond t = some false) el Q) :
    RelCT isa (Two (EAt H G P J)) (.ite cond th el) Q :=
  two_ite (fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ => by rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]) ht he

/-- In a branch, what its condition says of the entry state. -/
theorem e_branch {J J' : State → State → Prop} {cond : isa.Cond} {b : Bool} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ s t, EPre H s → J s t → isa.eval cond t = some b → J' s t)
    (hct : RelCT isa (Two (EAt H G P J')) c Q) :
    RelCT isa (Two fun a t => EAt H G P J a t ∧ isa.eval cond t = some b) c Q :=
  hct.mono (fun _ _ ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩ =>
    ⟨a, ⟨s₁, S₁, h _ _ S₁.1 j₁ e₁⟩, ⟨s₂, S₂, h _ _ S₂.1 j₂ e₂⟩⟩) fun _ _ h => h

/-! ## The call -/

theorem entryBytes {s t : State} (he : EnvE s t) (rd wr : List Region)
    {p : Addr} {len : Nat} (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩)
    (hs : (scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  have hfe : Frame [below (fb s) 16] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, he.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide) (by decide))
  have hfE : FrE s t.callEntry.mem :=
    he.fr.trans (hfe.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
  rw [State.withRegions_mem]
  exact FrE.bytes hfE hk ho hs hl

theorem pw_sib {a s : State} (S : ESib H G P a s) (i : Nat) : pw s i = pw a i := by
  match i with
  | 0 => show off _ _ = off _ _; rw [S.arg (by decide)]
  | 1 => exact S.gpr (by decide)
  | 2 => show off _ _ = off _ _; rw [S.arg (by decide)]
  | _ + 3 => show _ - _ = _ - _; rw [S.arg (by decide)]

theorem e_entry_regs (t : State) (rd wr : List Region) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions rd wr).gpr =
      [t.gpr .rdi, t.gpr .rsi, t.gpr .rdx, t.gpr .rcx, t.gpr .r8, t.gpr .r9, t.gpr .rsp - 8] := by
  simp only [List.map_cons, List.map_nil, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]

/-! ## `encMain` -/

section
variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

/-- In the frame, after the checks, with the entry state's addresses of
statics. -/
def EK (D : Nat) (s t : State) : Prop :=
  EW s t ∧ 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat ∧ t.syms = s.syms

/-- The label's hash's public data. -/
def lq (a : State) : LQ := ⟨fb a, stackArg a 6, [outR a, scrR a], stackArg a 0, (stackArg a 1).toNat⟩

/-- The label's hash's public data with its table, the stack argument 10. -/
def lqtE (Hm : Hash) (a : State) : LQT :=
  ⟨lq a, stackArg a 10, a.syms Hm.initN, a.syms Hm.updN, a.syms Hm.finN⟩

omit hH KH hG KG mH mG in
/-- `EW` in a state with the flags of another. -/
theorem EW.after {s t t' : State} (h : EW s t) (k : Keep [] t t') (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) : EW s t' :=
  let ⟨V, W, R, hW⟩ := h.rep
  ⟨h.he.step k.2.1 k.2.2 (k.gpr (by simp)) (keep_cs3 k rfl) hmx (by rw [hm]; exact Frame.refl _ _),
    h.L.congr (k.gpr (by simp)) k.2.2 (by rw [hm]), V, W, hm ▸ R, hW⟩

omit hH KH hG KG mH mG in
/-- The table's address to its slot, from a state in the frame. -/
theorem ew_tabSlot {s t : State} {G' : Stream} {f : Impl.Mgf1.X86_64.Table.Fns} (h : EW s t)
    (T : Table.Tab G' f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t) :
    WP isa (.block (tabSlot 10)) t fun t' => (EW s t' ∧ word t'.mem (fb s) (8 * 35) = stackArg s 10) ∧
      t'.syms = t.syms := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  exact WP.mono (wp_good (block_good _ rfl) (tabSlot_ok h.L R T)) fun t' ⟨⟨k, L', R', sy⟩, sp, mx, f'⟩ =>
    ⟨⟨⟨h.he.step k.2.1 k.2.2 sp (keep_cs3 k (by decide)) mx f', L', V, _, R', fun k hk => by
      simp only [upd]; rw [ifn (by omega_using [hk])]; exact hW k hk⟩, by rw [R'.fr 35 (by decide)]; simp [upd]⟩, sy⟩

include hH mH in
/-- `EM` before masking, with the label's hash function that of the table at
the stack argument 10 (`hT`), whose address (`harg`) and functions'
addresses (`hsym`) the anchor's public data fixes. -/
theorem encEm_ct {f : Impl.Mgf1.X86_64.Table.Fns} (hgi : Table.FnsGood f.init) (hgu : Table.FnsGood f.upd)
    (hgf : Table.FnsGood f.fin)
    (hT : ∀ a s t, ESib mH.G mG.G P a s → EnvE s t → t.syms = s.syms →
      Table.Tab Hl.stream f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t)
    (harg : ∀ a s, ESib mH.G mG.G P a s → stackArg s 10 = stackArg a 10)
    (hsym : ∀ a s, ESib mH.G mG.G P a s →
      s.syms Hl.initN = a.syms Hl.initN ∧ s.syms Hl.updN = a.syms Hl.updN ∧ s.syms Hl.finN = a.syms Hl.finN) :
    RelCT isa (Two (EAt mH.G mG.G P (EK Hl.D))) (encEm Hl.stream f) (Two (EAt mH.G mG.G P (EK Hl.D))) := by
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  have hD65 : Hl.D < 65 := by omega
  unfold encEm seqs seqs seqs seqs seqs
  refine RelCT.seq (e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14] (by decide) nopin ⟨_, by taint_decide⟩)
    fun s t hs h => WP.mono_syms (ew_clearEm h.1) fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14, 31] (by decide) nopin
      ⟨_, copySeed_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono_syms (ew_copySeed hs (Hm := Hl.stream) mH.len (by omega_using [hz]) (by omega_using [hz]) h.1)
      fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩) ?_
  -- The table's address to its slot.
  refine RelCT.seq (e_postS (J' := fun s t => EK Hl.D s t ∧ word t.mem (fb s) (8 * 35) = stackArg s 10)
    (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin etabSlot_taint)
    fun a s t S h => WP.mono (ew_tabSlot h.1 (hT a s t S h.1.he h.2.2)) fun _ ⟨⟨e, h35⟩, sy⟩ =>
      ⟨⟨e, h.2.1, sy.trans h.2.2⟩, h35⟩) ?_
  -- The label's hash.
  refine RelCT.seq (e_postS (J' := EK Hl.D) (two_map (lqtE Hl) (fun a t ⟨s, S, ⟨e, _, sy⟩, h35⟩ => by
      have hp := S.1
      obtain ⟨V, W, R, hW⟩ := e.rep
      have := (⟨⟨e.he.frv hp, e.L, V, W, R, e.lab hp hW⟩, h35, ⟨t, _, hT a s t S e.he sy, Table.TJ.refl t _, rfl, rfl⟩,
        by rw [sy]; rfl, by rw [sy]; rfl, by rw [sy]; rfl⟩ : LWT Hl.stream f 2 (lqtE Hl s) t)
      obtain ⟨y1, y2, y3⟩ := hsym a s S
      simp only [lqtE, lq] at this ⊢
      rwa [S.fb, S.out_eq, S.scr_eq, S.arg (i := 6) (by decide), S.arg (i := 0) (by decide),
        S.arg (i := 1) (by decide), harg a s S, y1, y2, y3] at this)
      (hashLabelT_ct hH.stream hgi hgu (.inl rfl) (Or.inl rfl)))
    fun a s t S h => WP.mono_syms (ew_hashLabelT S.1 hH mH hgi hgu hgf h.1.1 h.2 (hT a s t S h.1.1.he h.1.2.2))
      fun _ e sy => ⟨e, h.1.2.1, sy.trans h.1.2.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14] (by decide) nopin
      ⟨_, copyLh_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono_syms (ew_copyLh (Hm := Hl.stream) (by omega_using [hz]) (by omega_using [hz]) h.1)
      fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩) ?_
  exact e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14, 23, 29, 30] (by decide) nopin ⟨_, by taint_decide⟩)
    fun s t hs h => WP.mono_syms (ew_putMsg hs h.2.1 h.1) fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩


theorem fit_db {D : Nat} {s : State} {Hs : Spec.Mgf1.Hash} (hp : EPre Hs s)
    (hk : 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) :
    MFit (oEm + 1) D (oEm + 1 + D) ((s.gpr .rcx).toNat - (D + 1)) := by
  have := hp.k2
  exact ⟨by unfold oEm oSt; omega_using [hk, this], by unfold oEm oSt; omega_using [hk, this], by omega_using [], by omega_using [hk], by omega_using [this]⟩

theorem fit_seed {D : Nat} {s : State} {Hs : Spec.Mgf1.Hash} (hp : EPre Hs s)
    (hk : 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) (hD : 0 < D) :
    MFit (oEm + 1 + D) ((s.gpr .rcx).toNat - (D + 1)) (oEm + 1) D := by
  have := hp.k2
  exact ⟨by unfold oEm oSt; omega_using [hk, this], by unfold oEm oSt; omega_using [hk, this], by omega_using [], by omega_using [hD], by omega_using [hk, this]⟩

/-- Where MGF1 starts, for the anchor's public data. -/
theorem me_of {src srcLen dst dstLen : Nat → Nat} {a s t : State} (S : ESib H G P a s)
    (h : EWM s t (src (s.gpr .rcx).toNat) (srcLen (s.gpr .rcx).toNat) (dst (s.gpr .rcx).toNat)
      (dstLen (s.gpr .rcx).toNat))
    (hf : MFit (src (s.gpr .rcx).toNat) (srcLen (s.gpr .rcx).toNat) (dst (s.gpr .rcx).toNat)
      (dstLen (s.gpr .rcx).toNat)) :
    ME 2 ⟨fb a, stackArg a 6, [outR a, scrR a], src (a.gpr .rcx).toNat, srcLen (a.gpr .rcx).toNat,
      dst (a.gpr .rcx).toNat, dstLen (a.gpr .rcx).toNat⟩ t := by
  have hp := S.1
  obtain ⟨V, W, R, _, A⟩ := h.rep
  have := (⟨h.he.frv hp, h.L, hf, V, W, R, A⟩ : ME 2 ⟨fb s, stackArg s 6, [outR s, scrR s],
    src (s.gpr .rcx).toNat, srcLen (s.gpr .rcx).toNat, dst (s.gpr .rcx).toNat, dstLen (s.gpr .rcx).toNat⟩ t)
  rwa [S.fb, S.out_eq, S.scr_eq, S.arg (i := 6) (by decide), S.k] at this

/-! ## The checks -/

omit hH KH hG KG mH mG in
theorem zeroOut_ct : RelCT isa (Two (EAt H G P EW)) zeroOut fun _ _ => True :=
  e_taintF (fun _ _ _ h => h) [] [21, 23] (by decide) nopin ⟨_, by taint_decide⟩

/-- After the check of `k`. -/
def J2 (D : Nat) (s t : State) : Prop :=
  EW s t ∧ t.gpr .rax = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ t.cf = some (decide ((s.gpr .rcx).toNat < 2 * D + 2)) ∧
    t.syms = s.syms

/-- After the check of `k`, which passed. -/
def J2' (D : Nat) (s t : State) : Prop :=
  EW s t ∧ t.gpr .rax = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ 2 * D + 2 ≤ (s.gpr .rcx).toNat ∧ t.syms = s.syms

/-- After the check of the message's length. -/
def J3 (D : Nat) (s t : State) : Prop :=
  EW s t ∧ 2 * D + 2 ≤ (s.gpr .rcx).toNat ∧
    t.cf = some (decide ((s.gpr .rcx).toNat - (2 * D + 2) < (stackArg s 3).toNat)) ∧ t.syms = s.syms

theorem cf_false {t : State} {p : Prop} [Decidable p] (h : t.cf = some (decide p))
    (e : isa.eval .b t = some false) : ¬ p := by
  have e' : t.cf = some false := e
  rw [h] at e'
  simpa using e'

omit KH KG in
theorem chkMsg_step {s t : State} (hs : EPre mH.G s) (h : J2' Hl.D s t) :
    WP isa (.block (chkMsg Hl.stream)) t (J3 Hl.D s) := by
  have hp := hs
  have hk1 := hp.k1; have hk2 := hp.k2
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  obtain ⟨e, hax, hk, hsy⟩ := h
  obtain ⟨V, W, R, hW⟩ := e.rep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, w30, -⟩ := hW.w
  refine WP.mono_syms (wp_good (block_good _ rfl) (chkMsg_ok (Hm := Hl.stream) e.L R (k := (s.gpr .rcx).toNat)
    (mLen := (stackArg s 3).toNat) (by rw [w30, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hax (by omega_using [hk2])
    (by omega_using [hsD, hk]) (stackArg s 3).isLt (by omega_using [hz])))
    fun t3 ⟨⟨k3, hm3, hcf3⟩, sp3, mx3, f3⟩ sy => ⟨⟨e.he.step k3.2.1 k3.2.2 sp3 (keep_cs3 k3 (by decide)) mx3 f3,
      e.L.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3]), V, W, hm3 ▸ R, hW⟩, hk, by rw [hcf3, hsD], sy.trans hsy⟩

/-- After the prologue. -/
def JA (s t : State) : Prop := t = allocState frameBytes s

include hH mH mG in
/-- The prologue, the branch on the digest length of the table at the stack
argument 10 (`hT`, `harg`) and the checks, then `main`, constant time if
`main` is. -/
theorem encBodyWith_ct {f : Impl.Mgf1.X86_64.Table.Fns} {main : Nat → Prog isa}
    (hT : ∀ a s t, ESib mH.G mG.G P a s → EnvE s t → t.syms = s.syms →
      Table.Tab Hl.stream f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t)
    (harg : ∀ a s, ESib mH.G mG.G P a s → stackArg s 10 = stackArg a 10)
    (hmain : RelCT isa (Two (EAt mH.G mG.G P (EK Hl.D))) (main Hl.D) fun _ _ => True) :
    RelCT isa (Two (EAt mH.G mG.G P JA)) (encBodyWith main) fun _ _ => True := by
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  have hD65 : Hl.D < 65 := by omega
  have hDl : Hl.D ∈ lens := by rw [← mH.len]; exact mem_lens mH.mem
  unfold encBodyWith seqs seqs seqs
  -- The prologue.
  refine RelCT.seq (e_post (J' := fun s t => EW s t ∧ t.syms = s.syms)
    (two_taint [.rsp] (e_pins_rsp fun s t _ h => by rw [h]; rfl) pro_taint)
    fun s t hs h => by
      subst h
      exact WP.mono_syms (encHead_ok hs) fun t1 ⟨he1, L1, R1⟩ sy => ⟨⟨he1, L1, _, _, R1, fun _ _ => rfl⟩, sy⟩) ?_
  -- The table's address to its slot, and its digest length to `r11`.
  refine RelCT.seq (e_postS (J' := fun s t => (EW s t ∧ word t.mem (fb s) (8 * 35) = stackArg s 10) ∧
      t.syms = s.syms)
    (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin etabSlot_taint)
    fun a s t S h => WP.mono (ew_tabSlot h.1 (hT a s t S h.1.he h.2)) fun _ ⟨e, sy⟩ => ⟨e, sy.trans h.2⟩) ?_
  refine RelCT.seq (e_postS (J' := fun s t => EW s t ∧ t.syms = s.syms ∧ t.gpr .r11 = BitVec.ofNat 64 Hl.D)
    (two_taintF [] [35] fb (fun a => [outR a, scrR a]) (fun a _ => stackArg a 10)
      (fun a t ⟨s, S, ⟨⟨e, h35⟩, _⟩⟩ => by
        rw [← S.fb, ← S.out_eq, ← S.scr_eq, ← harg a s S]
        refine ⟨e.he.frv S.1, fun k hk => ?_⟩
        simp only [List.mem_singleton] at hk; subst hk
        exact h35)
      nopin (by decide) elenLoad_taint)
    fun a s t S h => by
      obtain ⟨⟨e, h35⟩, sy⟩ := h
      obtain ⟨V, W, R, hW⟩ := e.rep
      have T := hT a s t S e.he sy
      exact WP.mono (wp_good (block_good _ rfl) (lenLoad_ok e.L R ((R.fr 35 (by decide)).symm.trans h35) T.rdD
          (T.mem _ (Frame.refl _ _)).2.1))
        fun t' ⟨⟨k, h11, hm, sy'⟩, sp, mx, f'⟩ => ⟨⟨e.he.step k.2.1 k.2.2 sp (keep_cs3 k (by decide)) mx f',
          e.L.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), V, W, hm ▸ R, hW⟩, sy'.trans sy, h11⟩) ?_
  -- The checks for that length.
  refine byLen_ct (fun _ => Hl.D) cmpLens_taint (fun a t ⟨_, _, ⟨_, _, h11⟩⟩ => ⟨h11, hDl, mem_lens_lt hDl⟩)
    fun d _ => ?_
  by_cases hdd : Hl.D = d
  swap
  · exact RelCT.of_false fun _ _ ⟨_, ⟨_, e⟩, _⟩ => hdd e
  subst hdd
  rw [encChecks_D (G := ofLen Hl.D) (G' := Hl.stream) rfl]
  refine (?_ : RelCT isa (Two (EAt mH.G mG.G P fun s t => EW s t ∧ t.syms = s.syms))
    (encChecks Hl.stream (main Hl.D)) _).mono (fun _ _ ⟨a, ⟨⟨t₁, ⟨s₁, S₁, j₁⟩, k₁, m₁, y₁, x₁⟩, _⟩,
      ⟨⟨t₂, ⟨s₂, S₂, j₂⟩, k₂, m₂, y₂, x₂⟩, _⟩⟩ =>
    ⟨a, ⟨s₁, S₁, j₁.1.after k₁ m₁ x₁, y₁.trans j₁.2.1⟩, ⟨s₂, S₂, j₂.1.after k₂ m₂ x₂, y₂.trans j₂.2.1⟩⟩)
    fun _ _ h => h
  unfold encChecks seqs seqs seqs
  refine RelCT.seq (e_post (J' := J2 Hl.D) (two_taint [.rsp] (e_pins_rsp fun s t _ h => h.1.he.rsp)
      (chkK_taint Hl.D hD65))
    fun s t hs h => by
      obtain ⟨e, sy⟩ := h
      obtain ⟨V, W, R, hW⟩ := e.rep
      obtain ⟨-, -, -, w23, -⟩ := hW.w
      have hk1 := hs.k1; have hk2 := hs.k2
      exact WP.mono_syms (wp_good (block_good _ rfl) (chkK_ok (Hm := Hl.stream) e.L R
          (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_using [hk2]) (by omega_using [hz])))
        fun t2 ⟨⟨k2, hm2, hax2, hcf2⟩, sp2, mx2, f2⟩ sy2 => ⟨⟨e.he.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide))
          mx2 f2, e.L.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), V, W, hm2 ▸ R, hW⟩, hax2,
          by rw [hcf2, hsD], sy2.trans sy⟩) ?_
  refine e_ite (fun s => some (decide ((s.gpr .rcx).toNat < 2 * Hl.D + 2))) (fun s t h => h.2.2.1)
    (fun a s S => by rw [S.k]) (e_branch (J' := EW) (fun _ _ _ h _ => h.1) zeroOut_ct)
    (e_branch (J' := J2' Hl.D) (fun s t _ h e => ⟨h.1, h.2.1, by have := cf_false h.2.2.1 e; omega_using [this], h.2.2.2⟩) ?_)
  refine RelCT.seq (e_post (J' := J3 Hl.D) (two_taint [.rsp] (e_pins_rsp fun s t _ h => h.1.he.rsp)
      (chkMsg_taint Hl.D hD65)) fun s t hs h => chkMsg_step (hH := hH) (mH := mH) hs h) ?_
  refine e_ite (fun s => some (decide ((s.gpr .rcx).toNat - (2 * Hl.D + 2) < (stackArg s 3).toNat)))
    (fun s t h => h.2.2.1) (fun a s S => by rw [S.k, S.arg (i := 3) (by decide)])
    (e_branch (J' := EW) (fun _ _ _ h _ => h.1) zeroOut_ct)
    (e_branch (J' := EK Hl.D) (fun s t _ h e => ⟨h.1, by have := cf_false h.2.2.1 e; have := h.2.1; omega_arith,
      h.2.2.2⟩) hmain)

/-! ## The frame -/

omit hH KH hG KG mH mG in
theorem alloc_push {s s₁ : State} (h : isa.push (.alloc frameBytes) s = some s₁) :
    s₁ = allocState frameBytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

omit hH KH hG KG mH mG in
/-- A frame of `frameBytes` bytes leaks what its body does. -/
theorem relCT_alloc {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState frameBytes s₁ ∧ b = allocState frameBytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc frameBytes) body (.free frameBytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := alloc_push p₁
      obtain rfl := alloc_push p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

end

end VG.Proof.RsaOaep.X86_64
