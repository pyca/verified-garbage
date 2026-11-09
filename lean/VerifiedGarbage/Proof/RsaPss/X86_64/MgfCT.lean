module

public import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# RSASSA-PSS on x86-64: MGF1 is constant time

Two runs of `mgfXor H g` with the same frame, working space, writable
regions, place and length of `DB`, and addresses of statics (`MA`) leak the
same trace (`mgfXor_ct`): the loop runs once per `hLen` bytes of `DB` in
both, each round's pieces between the calls are checked by the taint
analysis (`FixedChecks`, `HashChecks`), and each call through a slot of the
table of `Hash` is of the same streaming function of `G` in both runs
(`two_scall`), whose arguments agree (`two_init`, `two_upd`, `two_fin`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.Bignum (off)
open VG.Proof.Bignum.X86_64 (Two two_post two_map two_loop)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)
open VG.Impl.Mgf1.X86_64.Table (Fns)

/-- What two runs of `mgfXor` share: the frame, the working space, the
writable regions after the frame, `DB`'s offset and length, and the
addresses of statics. -/
structure MA where
  F : Addr
  S : Addr
  rest : List Region
  e : Nat
  db : Nat
  sy : String → Addr

/-- The public words in round `j`: `scratch`, `DB`, `dbLen`, the seed, the
counter, the bytes done, and the slots of the table of `Hash`. -/
def mws (G : Stream) (D : Nat) (a : MA) (j : Nat) : List (Nat × BitVec 64) :=
  [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db), (29, off a.S (a.e + a.db)), (30, BitVec.ofNat 64 D),
    (31, BitVec.ofNat 64 j), (32, BitVec.ofNat 64 (j * G.D)), (14, BitVec.ofNat 64 G.D), (11, a.sy G.initN),
    (12, a.sy G.updN), (13, a.sy G.finN)]

/-- The rounds of `dbLen` bytes, `hLen` at a time. -/
def mN (D : Nat) (a : MA) : Nat := (a.db + D - 1) / D

theorem cnt_iff {j D db : Nat} (hD : 0 < D) : j < (db + D - 1) / D ↔ j * D < db := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hD, Nat.succ_mul]
  omega_arith

variable {G : Stream} (hG : StreamOK G) {g : Fns} {n : Nat} {H : Hash}
variable {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
  (hGv : Proof.Mgf1.Valid Gs)

variable (G g n H) in
/-- The anchor fits `mgfXor`, and the calls of `g` reach `G`'s functions. -/
def MOk (a : MA) : Prop := RestOk n a.F a.rest ∧ DbAt H.D a.e a.db

variable (G g) in
/-- A run's symbols `sy'`: the calls of `g` reach `G`'s functions, whose
addresses are the anchor's, `sy`. The runs agree on these names alone. -/
def SyG (sy sy' : String → Addr) : Prop :=
  GTF G g sy' ∧ sy' G.initN = sy G.initN ∧ sy' G.updN = sy G.updN ∧ sy' G.finN = sy G.finN

theorem SyG.tr {sy s₁ s₂ : String → Addr} (h : SyG G g sy s₂) (e : s₁ = s₂) : SyG G g sy s₁ := e ▸ h

theorem mws_gt {D : Nat} {a : MA} {j : Nat} {sy : String → Addr} {W : Nat → BitVec 64} (hok : SyG G g a.sy sy)
    (hw : ∀ q ∈ mws G D a j, W q.1 = q.2) : GT G g W sy :=
  hok.1.gt ((hw (11, a.sy G.initN) (by simp only [mws, List.mem_cons, true_or, or_true])).trans hok.2.1.symm)
    ((hw (12, a.sy G.updN) (by simp only [mws, List.mem_cons, true_or, or_true])).trans hok.2.2.1.symm)
    ((hw (13, a.sy G.finN) (by simp only [mws, List.mem_cons, true_or, or_true])).trans hok.2.2.2.symm)
    (hw (14, BitVec.ofNat 64 G.D) (by simp only [mws, List.mem_cons, true_or, or_true]))

variable (G g n H) in
/-- A point of round `j`: the public words as they are at its start. -/
structure RP (a : MA) (j : Nat) (t : State) : Prop where
  ok : MOk n H a
  lt : j * G.D < a.db
  pub : Pub a.F a.S a.rest (mws G H.D a j) [] (fun _ _ => True) t
  sy : SyG G g a.sy t.syms

theorem RP.after {a : MA} {j : Nat} {t t' : State} (h : RP G g n H a j t) (L' : Lay t' a.F a.S)
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W : Nat → BitVec 64} (R' : Rep t'.mem a.F a.S V' W)
    (hw : ∀ q ∈ mws G H.D a j, W q.1 = q.2) (hs : t'.syms = t.syms) : RP G g n H a j t' :=
  ⟨h.ok, h.lt, h.pub.next L' hwr R' hw trivial, h.sy.tr hs⟩

theorem RP.keepM {a : MA} {j : Nat} {t t' : State} (h : RP G g n H a j t) (hsp : t'.gpr .rsp = t.gpr .rsp)
    (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem) (hs : t'.syms = t.syms) : RP G g n H a j t' :=
  ⟨h.ok, h.lt, h.pub.keepM hsp hwr hm, h.sy.tr hs⟩

theorem RP.sub {a : MA} {j : Nat} {t : State} (h : RP G g n H a j t) {ws : List (Nat × BitVec 64)}
    (hws : ∀ q ∈ ws, q ∈ mws G H.D a j) : Pub a.F a.S a.rest ws [] (fun _ _ => True) t :=
  h.pub.sub hws (fun _ h => h) fun _ _ x => x

/-! ## A round -/

variable (G g n H) in
abbrev Q0 (p : MA × Nat) (t : State) : Prop := RP G g n H p.1 p.2 t

variable (G g n H) in
abbrev Q1 (p : MA × Nat) (t : State) : Prop := RP G g n H p.1 p.2 t ∧ t.gpr .rdi = off p.1.S oSt

variable (G g n H) in
abbrev Q3 (p : MA × Nat) (t : State) : Prop :=
  RP G g n H p.1 p.2 t ∧ t.gpr .rdi = off p.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 0 ∧
    t.gpr .rdx = off p.1.S (p.1.e + p.1.db) ∧ t.gpr .rcx = BitVec.ofNat 64 H.D ∧ t.gpr .r8 = off p.1.S oCW

variable (G g n H) in
abbrev Q5 (p : MA × Nat) (t : State) : Prop :=
  RP G g n H p.1 p.2 t ∧ t.gpr .rdi = off p.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 H.D ∧
    t.gpr .rdx = off p.1.S oLen ∧ t.gpr .rcx = BitVec.ofNat 64 4 ∧ t.gpr .r8 = off p.1.S oCW

variable (G g n H) in
abbrev Q7 (p : MA × Nat) (t : State) : Prop :=
  RP G g n H p.1 p.2 t ∧ t.gpr .rdi = off p.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 (H.D + 4) ∧
    t.gpr .rdx = off p.1.S oDig ∧ t.gpr .rcx = off p.1.S oCW

theorem mws_w {D : Nat} {a : MA} {j : Nat} {W : Nat → BitVec 64} (hw : ∀ q ∈ mws G D a j, W q.1 = q.2) :
    W 14 = BitVec.ofNat 64 G.D ∧ W 23 = off a.S a.e ∧ W 24 = BitVec.ofNat 64 a.db ∧
      W 29 = off a.S (a.e + a.db) ∧ W 30 = BitVec.ofNat 64 D ∧ W 31 = BitVec.ofNat 64 j ∧
      W 32 = BitVec.ofNat 64 (j * G.D) :=
  have m : ∀ {q}, q ∈ mws G D a j → W q.1 = q.2 := fun h => hw _ h
  ⟨m (q := (14, BitVec.ofNat 64 G.D)) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (23, off a.S a.e)) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (24, BitVec.ofNat 64 a.db)) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (29, off a.S (a.e + a.db))) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (30, BitVec.ofNat 64 D)) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (31, BitVec.ofNat 64 j)) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (32, BitVec.ofNat 64 (j * G.D))) (by simp only [mws, List.mem_cons, true_or, or_true])⟩

include hG in
theorem round_ct (hfx : FixedChecks n) :
    RelCT isa (Two (Q0 G g n H)) (mgfRound g) fun _ _ => True := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have c1 : oSt = 2048 := rfl
  have c2 : oDig = 2304 := rfl
  have c3 : oLen = 2368 := rfl
  have c4 : oCW = 0 := rfl
  have c5 : oRsa = 8192 := rfl
  have c6 : oEm = 2560 := rfl
  obtain ⟨_, hmgfIni⟩ := hfx.mgfIni
  obtain ⟨_, hmgfSrc⟩ := hfx.mgfSrc
  obtain ⟨_, hmgfCtr⟩ := hfx.mgfCtr
  obtain ⟨_, hmgfFin⟩ := hfx.mgfFin
  obtain ⟨_, hmgfXorOut⟩ := hfx.mgfXorOut
  obtain ⟨_, hmgfNext⟩ := hfx.mgfNext
  unfold mgfRound seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine RelCT.seq (two_post (Ψ := Q1 G g n H) (two_pub n [21] [] (fun p => p.1.F) (fun p => p.1.S)
      (fun p => p.1.rest) (fun p => [(21, p.1.S)]) (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
        rw [List.mem_singleton.mp hq]; simp only [mws, List.mem_cons, true_or]⟩)
      (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfIni)
    fun p t h => X86_64.WP.mono_syms (scr_ok h.pub.L (d := .rdi) (by decide) (o := oSt) (by decide))
      fun t' ⟨hdi, hm, k⟩ sy => ⟨h.keepM (k.gpr (by decide)) k.2.2 hm sy, hdi⟩) ?_
  refine RelCT.seq (two_post (Ψ := Q0 G g n H) (two_scall n (s := sIniG) (by decide) (fun p => p.1.F)
      (fun p => p.1.S) (fun p => p.1.rest) (fun p => p.1.sy G.initN)
      (fun p t h => ⟨h.1.pub.L, h.1.pub.wr, h.1.ok.1, pub_slot h.1.pub (k := 11) rfl (by decide) (by simp only [mws, List.mem_cons, true_or, or_true]),
        h.1.sy.2.1, h.1.sy.1.fi⟩) (hfx.ld _ (.inr (.inr (.inr (.inl rfl)))))
      (two_init hG (fun p => p.1.F) (fun p => p.1.S) fun p t ⟨t₀, h, k, hm, _⟩ =>
        ⟨lay_keep11 h.1.pub.L k hm, (k.gpr (by decide)).trans h.2⟩)) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.1.pub.W
    exact X86_64.WP.mono_syms (initS_ok hG h.1.pub.L R (mws_gt h.1.sy hw) h.2)
      fun t' ⟨L', _, wr', _, R', _⟩ sy => h.1.after L' wr' R' hw sy
  -- `update` with the seed.
  refine RelCT.seq (two_post (Ψ := Q3 G g n H) (two_pub n [21, 29, 30] [] (fun p => p.1.F) (fun p => p.1.S)
      (fun p => p.1.rest) (fun p => [(21, p.1.S), (29, off p.1.S (p.1.e + p.1.db)), (30, BitVec.ofNat 64 H.D)])
      (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> simp only [mws, List.mem_cons, true_or, or_true]⟩)
      (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfSrc) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.pub.W
    have w := mws_w hw
    exact X86_64.WP.mono_syms (updSrc_ok h.pub.L R w.2.2.2.1 w.2.2.2.2.1)
      fun t' ⟨hdi, hsi, hdx, hcx, h8, hm, k⟩ sy => ⟨h.keepM (k.gpr (by decide)) k.2.2 hm sy, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := Q0 G g n H) (two_scall n (s := sUpdG) (by decide) (fun p => p.1.F)
      (fun p => p.1.S) (fun p => p.1.rest) (fun p => p.1.sy G.updN)
      (fun p t h => ⟨h.1.pub.L, h.1.pub.wr, h.1.ok.1, pub_slot h.1.pub (k := 12) rfl (by decide) (by simp only [mws, List.mem_cons, true_or, or_true]),
        h.1.sy.2.2.1, h.1.sy.1.fu⟩) (hfx.ld _ (.inr (.inr (.inr (.inr (.inl rfl))))))
      (two_upd hG (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.e + p.1.db) (fun _ => H.D)
        (fun _ => BitVec.ofNat 64 0) fun p t ⟨t₀, h, k, hm, _⟩ => by
          have := h.1.ok.2.fit; have := h.1.ok.2.e1
          exact ⟨lay_keep11 h.1.pub.L k hm, by omega_arith, Or.inr (by omega_arith), Or.inr (by omega_arith),
            (k.gpr (by decide)).trans h.2.1, (k.gpr (by decide)).trans h.2.2.1, (k.gpr (by decide)).trans h.2.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2.2⟩)) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.1.pub.W
    have := h.1.ok.2.fit; have := h.1.ok.2.e1
    exact X86_64.WP.mono_syms (updS_ok hG h.1.pub.L R (mws_gt h.1.sy hw)
        (a := p.1.e + p.1.db) (len := H.D) (by omega_arith) (Or.inr (by omega_arith)) (Or.inr (by omega_arith))
        h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
      fun t' ⟨L', _, wr', _, R', _⟩ sy => h.1.after L' wr' R' hw sy
  -- The counter, and `update` with it.
  refine RelCT.seq (two_post (Ψ := Q5 G g n H) (two_pub n [21, 30, 31] [] (fun p => p.1.F) (fun p => p.1.S)
      (fun p => p.1.rest) (fun p => [(21, p.1.S), (30, BitVec.ofNat 64 H.D), (31, BitVec.ofNat 64 p.2)])
      (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> simp only [mws, List.mem_cons, true_or, or_true]⟩)
      (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfCtr) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.pub.W
    have w := mws_w hw
    have := h.lt; have := h.ok.2.fit; have := h.ok.2.e1
    have hc : p.2 ≤ p.2 * G.D := Nat.le_mul_of_pos_right _ hzD
    exact X86_64.WP.mono_syms (updCtr_ok h.pub.L R w.2.2.2.2.1 w.2.2.2.2.2.1 (by omega_arith))
      fun t' ⟨L', hdi, hsi, hdx, hcx, h8, k, R'⟩ sy => ⟨h.after L' k.2.2 R' hw sy, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := Q0 G g n H) (two_scall n (s := sUpdG) (by decide) (fun p => p.1.F)
      (fun p => p.1.S) (fun p => p.1.rest) (fun p => p.1.sy G.updN)
      (fun p t h => ⟨h.1.pub.L, h.1.pub.wr, h.1.ok.1, pub_slot h.1.pub (k := 12) rfl (by decide) (by simp only [mws, List.mem_cons, true_or, or_true]),
        h.1.sy.2.2.1, h.1.sy.1.fu⟩) (hfx.ld _ (.inr (.inr (.inr (.inr (.inl rfl))))))
      (two_upd hG (fun p => p.1.F) (fun p => p.1.S) (fun _ => oLen) (fun _ => 4)
        (fun _ => BitVec.ofNat 64 H.D) fun p t ⟨t₀, h, k, hm, _⟩ =>
          ⟨lay_keep11 h.1.pub.L k hm, by omega_arith, Or.inr (by omega_arith), Or.inr (by omega_arith),
            (k.gpr (by decide)).trans h.2.1, (k.gpr (by decide)).trans h.2.2.1, (k.gpr (by decide)).trans h.2.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2.2⟩)) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.1.pub.W
    exact X86_64.WP.mono_syms (updS_ok hG h.1.pub.L R (mws_gt h.1.sy hw)
        (a := oLen) (len := 4) (by omega_arith) (Or.inr (by omega_arith)) (Or.inr (by omega_arith))
        h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
      fun t' ⟨L', _, wr', _, R', _⟩ sy => h.1.after L' wr' R' hw sy
  -- `finalize`.
  refine RelCT.seq (two_post (Ψ := Q7 G g n H) (two_pub n [21, 30] [] (fun p => p.1.F) (fun p => p.1.S)
      (fun p => p.1.rest) (fun p => [(21, p.1.S), (30, BitVec.ofNat 64 H.D)])
      (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> simp only [mws, List.mem_cons, true_or, or_true]⟩)
      (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfFin) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.pub.W
    have w := mws_w hw
    exact X86_64.WP.mono_syms (finA_ok h.pub.L R w.2.2.2.2.1)
      fun t' ⟨hdi, hsi, hdx, hcx, hm, k⟩ sy => ⟨h.keepM (k.gpr (by decide)) k.2.2 hm sy, hdi, hsi, hdx, hcx⟩
  refine RelCT.seq (two_post (Ψ := Q0 G g n H) (two_scall n (s := sFinG) (by decide) (fun p => p.1.F)
      (fun p => p.1.S) (fun p => p.1.rest) (fun p => p.1.sy G.finN)
      (fun p t h => ⟨h.1.pub.L, h.1.pub.wr, h.1.ok.1, pub_slot h.1.pub (k := 13) rfl (by decide) (by simp only [mws, List.mem_cons, true_or, or_true]),
        h.1.sy.2.2.2, h.1.sy.1.ff⟩) (hfx.ld _ (.inr (.inr (.inr (.inr (.inr rfl))))))
      (two_fin hG (fun p => p.1.F) (fun p => p.1.S) (fun _ => oDig) (fun _ => BitVec.ofNat 64 (H.D + 4))
        fun p t ⟨t₀, h, k, hm, _⟩ =>
          ⟨lay_keep11 h.1.pub.L k hm, ⟨by omega_arith, by omega_arith⟩, (k.gpr (by decide)).trans h.2.1,
            (k.gpr (by decide)).trans h.2.2.1, (k.gpr (by decide)).trans h.2.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.2⟩)) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.1.pub.W
    exact X86_64.WP.mono_syms (finS_ok hG h.1.pub.L R (mws_gt h.1.sy hw) (o := oDig)
        ⟨by omega_arith, by omega_arith⟩ h.2.1 h.2.2.2.1 h.2.2.2.2)
      fun t' ⟨L', _, wr', _, R', _⟩ sy => h.1.after L' wr' R' hw sy
  -- Into `DB`, and the next counter.
  refine RelCT.seq (two_post (Ψ := Q0 G g n H) (two_pub n [14, 21, 23, 24, 32] [] (fun p => p.1.F)
      (fun p => p.1.S) (fun p => p.1.rest)
      (fun p => [(14, BitVec.ofNat 64 G.D), (21, p.1.S), (23, off p.1.S p.1.e), (24, BitVec.ofNat 64 p.1.db),
        (32, BitVec.ofNat 64 (p.2 * G.D))])
      (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp only [mws, List.mem_cons, true_or, or_true]⟩)
      (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfXorOut) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.pub.W
    have w := mws_w hw
    have := h.ok.2.fit; have := h.ok.2.e1
    exact X86_64.WP.mono_syms (xorOut_ok (G := G) h.pub.L R (dst := p.1.e) (dstLen := p.1.db) (done := p.2 * G.D)
        (by omega_arith) (by omega_arith) hzD (by omega_arith) w.1 w.2.1 w.2.2.1 w.2.2.2.2.2.2 h.lt)
      fun t' ⟨L', k, R'⟩ sy => h.after L' k.2.2 R' hw sy
  exact two_pub n [14, 24, 31, 32] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => [(14, BitVec.ofNat 64 G.D), (24, BitVec.ofNat 64 p.1.db), (31, BitVec.ofNat 64 p.2),
      (32, BitVec.ofNat 64 (p.2 * G.D))])
    (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [mws, List.mem_cons, true_or, or_true]⟩)
    (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfNext

/-! ## The loop -/

variable (G g n H) in
/-- Before round `j`: the correctness proof's invariant. -/
def MI (a : MA) (j : Nat) (t : State) : Prop :=
  MOk n H a ∧ j * G.D < a.db ∧ ∃ (u₀ : State) (V : Nat → Byte) (W : Nat → BitVec 64),
    u₀.wr = ⟨a.F, frameBytes⟩ :: a.rest ∧ SyG G g a.sy u₀.syms ∧ W 21 = a.S ∧ W 23 = off a.S a.e ∧
    W 24 = BitVec.ofNat 64 a.db ∧ W 29 = off a.S (a.e + a.db) ∧ W 30 = BitVec.ofNat 64 H.D ∧ GT G g W u₀.syms ∧
    MgfI u₀ a.F a.S V W (Spec.Mgf1.mgf1 Gs ((List.range H.D).map fun i => V (a.e + a.db + i)) a.db)
      a.e a.db G.D j t

theorem mi_rp {a : MA} {j : Nat} {t : State} (h : MI G g n H (Gs := Gs) a j t) : RP G g n H a j t := by
  obtain ⟨hok, hj, u₀, V, W, hwr, hsy, h21, h23, h24, h29, h30, T, I⟩ := h
  obtain ⟨V', W', R', h31, h32, hW, -⟩ := I.rep
  have e : ∀ k, k < nW → k ≠ 31 → k ≠ 32 → W' k = W k := hW
  refine ⟨hok, hj, ⟨I.L, I.wr.trans hwr, ⟨V', W', R', fun q hq => ?_, trivial⟩, fun _ hp => by cases hp⟩,
    hsy.tr I.sy⟩
  simp only [mws, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (e 21 (by decide) (by decide) (by decide)).trans h21
  · exact (e 23 (by decide) (by decide) (by decide)).trans h23
  · exact (e 24 (by decide) (by decide) (by decide)).trans h24
  · exact (e 29 (by decide) (by decide) (by decide)).trans h29
  · exact (e 30 (by decide) (by decide) (by decide)).trans h30
  · exact h31
  · exact h32
  · exact (e 14 (by decide) (by decide) (by decide)).trans T.wd
  · exact (e 11 (by decide) (by decide) (by decide)).trans (T.wi.trans hsy.2.1)
  · exact (e 12 (by decide) (by decide) (by decide)).trans (T.wu.trans hsy.2.2.1)
  · exact (e 13 (by decide) (by decide) (by decide)).trans (T.wf.trans hsy.2.2.2)

include hG hGh hGl hGv in
theorem round_wp {a : MA} {j : Nat} {t : State} (h : MI G g n H (Gs := Gs) a j t) :
    WP isa (mgfRound g) t fun t' =>
      isa.eval .b t' = some (decide (j + 1 < mN G.D a)) ∧ (j + 1 < mN G.D a → MI G g n H (Gs := Gs) a (j + 1) t') ∧
      (j + 1 = mN G.D a → True) := by
  have hD := (sizes hG).2.2.2.2
  obtain ⟨hok, hjD, u₀, V, W, hwr, hsy, h21, h23, h24, h29, h30, T, I⟩ := h
  refine WP.mono (round_ok hG hGh hGl hGv hok.2 h23 h24 h29 h30 T I hjD) fun t' ⟨hcf, I'⟩ => ⟨?_, fun h' =>
    ⟨hok, (cnt_iff hD).mp h', u₀, V, W, hwr, hsy, h21, h23, h24, h29, h30, T, I'⟩, fun _ => trivial⟩
  simp only [eval, hcf, Option.some.injEq, decide_eq_decide]
  exact (cnt_iff hD).symm

variable (G g n H) in
/-- At the start: the public words of `DB` and the slots of the table of
`Hash`. -/
def ME (a : MA) (t : State) : Prop :=
  MOk n H a ∧ Pub a.F a.S a.rest [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db),
    (14, BitVec.ofNat 64 G.D), (11, a.sy G.initN), (12, a.sy G.updN), (13, a.sy G.finN)] [] (fun _ _ => True) t ∧
    SyG G g a.sy t.syms

include hG in
theorem mgfHead_ct (hc : HashChecks H.P H.D n) :
    RelCT isa (Two (ME G g n H))
      (.block (mgfSeed H ++ ([.mov32 .rax (.imm 0), .store (sp sCtr) .rax, .store (sp sDone) .rax] : List Instr)))
      (Two fun a t => 0 < mN G.D a ∧ MI G g n H (Gs := Gs) a 0 t) := by
  have hD := (sizes hG).2.2.2.2
  obtain ⟨_, hhd⟩ := hc.mgfHead
  refine two_post (two_pub n [21, 23, 24] [] MA.F MA.S MA.rest
    (fun a => [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db)]) (fun _ => [])
    (fun a t h => ⟨_, h.2.1.sub (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp) (fun _ h => h) fun _ _ x => x⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hhd) fun a t h => ?_
  obtain ⟨V, W, R, hw, -⟩ := h.2.1.W
  have hp : ∀ {k v}, (k, v) ∈ [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db),
      (14, BitVec.ofNat 64 G.D), (11, a.sy G.initN), (12, a.sy G.updN), (13, a.sy G.finN)] → W k = v :=
    fun hm => hw _ hm
  have hdb1 := h.1.2.db1
  refine X86_64.WP.mono_syms (mgfHead_ok H h.2.1.L R h.1.2 (hp (by simp)) (hp (by simp)))
    fun v ⟨Lv, hk, Rv⟩ sv => ?_
  let W₀ := upd (upd W 29 (off a.S (a.e + a.db))) 30 (BitVec.ofNat 64 H.D)
  have hW₀ : ∀ k, k ≠ 29 → k ≠ 30 → W₀ k = W k := fun k h1 h2 => by simp only [W₀, upd, ifn h1, ifn h2]
  have T₀ : GT G g W₀ v.syms := by
    rw [sv]
    exact h.2.2.1.gt (((hW₀ 11 (by decide) (by decide)).trans (hp (by simp))).trans h.2.2.2.1.symm)
      (((hW₀ 12 (by decide) (by decide)).trans (hp (by simp))).trans h.2.2.2.2.1.symm)
      (((hW₀ 13 (by decide) (by decide)).trans (hp (by simp))).trans h.2.2.2.2.2.symm)
      ((hW₀ 14 (by decide) (by decide)).trans (hp (by simp)))
  refine ⟨(cnt_iff hD).mpr (by rw [Nat.zero_mul]; omega_arith), h.1, by rw [Nat.zero_mul]; omega_arith, v, V, W₀,
    hk.2.2.trans h.2.1.wr, h.2.2.tr sv, (hW₀ 21 (by decide) (by decide)).trans (hp (by simp)),
    (hW₀ 23 (by decide) (by decide)).trans (hp (by simp)), (hW₀ 24 (by decide) (by decide)).trans (hp (by simp)),
    by simp [W₀, upd], by simp [W₀, upd], T₀,
    ⟨Lv, rfl, rfl, fun _ _ => rfl, rfl, _, _, Rv, by simp [upd], by simp [upd],
      fun k _ h1 h2 => by simp only [upd, ifn h2, ifn h1]; rfl,
      fun o _ _ => by simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]; rw [ifn (by omega_arith)]⟩⟩

include hG hGh hGl hGv in
/-- `mgfXor` is constant time. -/
theorem mgfXor_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (ME G g n H)) (mgfXor H g) fun _ _ => True :=
  (mgfHead_ct hG (Gs := Gs) hc).seq ((two_loop (Φ := MI G g n H (Gs := Gs)) (Ψ := fun _ _ => True) (mN G.D)
    (two_map id (fun _ _ h => mi_rp h.2) (round_ct hG hfx))
    fun _ _ _ _ h => round_wp hG hGh hGl hGv h).mono (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.RsaPss.X86_64
