module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

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
          exact ⟨lay_keep11 h.1.rw.L k hm, by omega, by omega, by omega, (k.gpr (by decide)).trans h.2.1,
            (k.gpr (by decide)).trans h.2.2.1, (k.gpr (by decide)).trans h.2.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2.2⟩))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.1.rw.rep
    have := h.1.rw.fit.fs
    exact WP.mono (wp_gs (tcall_good hgu 1) (updT_ok hG h.1.rw.L R (h.1.w35' R) h.1.tabAt (a := a.1.src)
      (len := a.1.srcLen) (by omega) (by omega) (by omega) h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2))
      fun t' ⟨⟨L', rd', wr', _, R', _⟩, fr, sy⟩ => h.1.after L' rd' wr' R R' A h19 h20 fr sy
  -- The counter, and `update` with it.
  refine RelCT.seq (two_pieceF (Ψ := P5T G f n) [] [14] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mwT G.D a.1 a.2) (fun a t h => h.words (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.rw.rep
    have := h.rw.lt
    have := h.rw.fit.dstB
    have hc : a.2 ≤ a.2 * G.D := Nat.le_mul_of_pos_right _ hzD
    exact WP.mono (wp_gs (block_good _ rfl) (updCtr_ok h.rw.L R A.hsl h19 (by omega)))
      fun t' ⟨⟨L', hdi, hsi, hdx, hcx, h8, k, R'⟩, fr, sy⟩ =>
        ⟨h.after L' k.2.1 k.2.2 R R' A h19 h20 fr sy, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := P0T G f n) (two_tcall 1 (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws)
      (fun a => a.1.p) (fun a => a.1.au)
      (fun a t h => ⟨h.1.rw.fv, h.1.rw.L, h.1.w35, h.1.tabAt.rd 1 (by decide), h.1.tabAt.mem.2.1.trans h.1.au,
        h.1.au, h.1.tabAt.ok.u⟩) (tload_taint hn 1 (by decide))
      (two_upd hG (fun a => a.1.F) (fun a => a.1.S) (fun _ => oCtr) (fun _ => 4)
        (fun a => BitVec.ofNat 64 a.1.srcLen) fun a t ⟨t₀, h, k, hm, _⟩ =>
          ⟨lay_keep11 h.1.rw.L k hm, by omega, by omega, by omega, (k.gpr (by decide)).trans h.2.1,
            (k.gpr (by decide)).trans h.2.2.1, (k.gpr (by decide)).trans h.2.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2.2⟩))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.1.rw.rep
    exact WP.mono (wp_gs (tcall_good hgu 1) (updT_ok hG h.1.rw.L R (h.1.w35' R) h.1.tabAt (a := oCtr) (len := 4)
      (by omega) (by omega) (by omega) h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2))
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
          ⟨lay_keep11 h.1.rw.L k hm, by omega, (k.gpr (by decide)).trans h.2.1, (k.gpr (by decide)).trans h.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2⟩))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.1.rw.rep
    exact WP.mono (wp_gs (tcall_good hgf 2) (finT_ok hG h.1.rw.L R (h.1.w35' R) h.1.tabAt (o := oDig) (by omega)
      h.2.1 h.2.2.2.1 h.2.2.2.2)) fun t' ⟨⟨L', rd', wr', _, R', _⟩, fr, sy⟩ => h.1.after L' rd' wr' R R' A h19 h20 fr sy
  -- Into `dst`, and the next counter.
  refine RelCT.seq (two_pieceF (Ψ := P0T G f n) [] [14, 17, 18, 20, 36] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mwT G.D a.1 a.2) (fun a t h => h.words (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.rw.rep
    have := h.rw.fit.fd
    exact WP.mono (wp_gs xorOutT_good (xorOutT_ok (G := G) h.rw.L R (dst := a.1.dst) (dstLen := a.1.dstLen)
        (done := a.2 * G.D) (by omega) hzD (by omega) (h.w36' R) A.hdst A.hdl h20 h.rw.lt))
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
      A.of_eq fun k h1 h2 => hW k (by unfold nW frameBytes; omega) (by omega) (by omega), h19, h20⟩,
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
      fun v ⟨⟨I, _⟩, fr, sy⟩ => ⟨(lt_nR hD q.toMQ 0).mpr (by omega), fv.congr (I.L.rsp.trans L.rsp.symm) I.wr,
        fit, t₀, sArg, V, upd (upd W 35 q.p) 36 (BitVec.ofNat 64 G.D),
        A.of_eq fun k h1 h2 => by simp only [upd]; rw [ifn (by omega), ifn (by omega)],
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
