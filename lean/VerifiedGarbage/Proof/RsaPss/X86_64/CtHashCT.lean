import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk
import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# RSASSA-PSS on x86-64: `ctHash` is constant time

Two runs of `ctHash` with the same frame, working space, writable regions
and number of blocks (`HA`), hashing messages of any lengths that fit in
them, leak the same trace (`ctHash_ct`): the pieces between the calls are
checked by the taint analysis (`HashChecks`), the calls are constant time by
their callees' contracts, and the loop over the blocks goes the same way in
both runs.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum.X86_64 (off Two two_post two_map two_mono two_loop)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initK)
open VG.Proof.MdStream.X86_64 (compressK)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- What two runs of `ctHash` share: the frame, the working space, the
writable regions after the frame and the number of blocks. -/
structure HA where
  F : Addr
  S : Addr
  rest : List Region
  nbm : Nat

/-- The public words: `scratch` and the number of blocks. -/
def hws (a : HA) : List (Nat × BitVec 64) := [(21, a.S), (28, BitVec.ofNat 64 a.nbm)]

theorem w21 {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) : W 21 = S := by
  have := L.slot
  rw [slot_eq sScr 21 rfl] at this
  rw [← R.fr 21 (by decide)]; exact this

variable {H : Hash} (hH : HashOK H) (K : Callees H) (n : Nat)

/-- The anchor fits `ctHash`. -/
def HOk (a : HA) : Prop := RestOk n a.F a.rest ∧ 1 ≤ a.nbm ∧ a.nbm * H.P.B ≤ 2048

variable (H) in
/-- At the start, and until the length field: the message's length `ℓ`
(secret) fits in the blocks. -/
def HE (a : HA) (t : State) : Prop :=
  HOk (H := H) n a ∧ Pub a.F a.S a.rest (hws a) []
    (fun _ W => ∃ ℓ, W 27 = BitVec.ofNat 64 ℓ ∧ ℓ + 1 + H.P.L ≤ a.nbm * H.P.B) t

/-- The taint checks of the pieces that do not depend on the hash function. -/
structure FixedChecks (n : Nat) : Prop where
  scrSt : ∃ hc, (taint.check (pT n [21, 28] []) (.block (scr .rdi oSt)) hc).isSome = true
  startB : ∃ hc, (taint.check (pT n [21, 28] []) (.block [.mov32 .rax (.imm 0), .store (sp sB) .rax]) hc).isSome
    = true
  nextB : ∃ hc, (taint.check (pT n [21, 28, 29] []) (.block nextBlock) hc).isSome = true
  mgfInit : ∃ hc, (taint.check (pT n [21, 23, 24] [])
    (.block [.mov32 .rax (.imm 0), .store (sp sCtr) .rax, .store (sp sDone) .rax]) hc).isSome = true

theorem fixedChecks {n : Nat} (hn : n = 1 ∨ n = 2) : FixedChecks n := by
  rcases hn with rfl | rfl
  · exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  · exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩


theorem Pub.sub {F S : Addr} {rest : List Region} {ws ws' : List (Nat × BitVec 64)} {rs rs' : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} {t : State} (h : Pub F S rest ws rs X t)
    (hws : ∀ p ∈ ws', p ∈ ws) (hrs : ∀ p ∈ rs', p ∈ rs) (hX : ∀ V W, X V W → X' V W) : Pub F S rest ws' rs' X' t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun p hp => hw p (hws p hp), hX V W hx⟩, fun p hp => h.regs p (hrs p hp)⟩

/-! ## The calls -/

/-- Before the call of `init`. -/
def IA (F S : Addr) (u : State) : Prop := Lay u F S ∧ u.gpr .rdi = off S oSt

include hH in
theorem init_pre {F S : Addr} {u : State} (h : IA F S u) :
    (initK (H.P.N + H.P.B) hH.SH.Repr).pre (u.callEntry.withRegions [] [⟨off S oSt, H.P.N + H.P.B⟩]) := by
  have hNB : H.P.N + H.P.B ≤ 192 := by have := hH.N_le; have := hH.B_le; omega
  simp only [initK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), h.2, h.1.rsp, true_and]
  exact Region.Disjoint.sub_right h.1.dRS (Offset.sub_base S (by unfold oSt oRsa; omega))

include hH in
theorem init_rel {P : State → State → Prop} (h : ∀ s₁ s₂, P s₁ s₂ → ∃ F S, IA F S s₁ ∧ IA F S s₂) :
    RelCT isa P (.call H.initN H.initC) fun _ _ => True := by
  have hNB : H.P.N + H.P.B ≤ 192 := by have := hH.N_le; have := hH.B_le; omega
  refine RelCT.callEx hH.init.1 hH.init.2.1 fun s₁ s₂ hp => ?_
  obtain ⟨F, S, h₁, h₂⟩ := h s₁ s₂ hp
  refine ⟨[], _, [], _, init_pre hH h₁, init_pre hH h₂, ?_, Covers.right (h₁.1.cov (by unfold oSt oRsa; omega)),
    h₁.1.cov (by unfold oSt oRsa; omega), Covers.right (h₂.1.cov (by unfold oSt oRsa; omega)),
    h₂.1.cov (by unfold oSt oRsa; omega), by rw [h₁.1.rsp, h₂.1.rsp]⟩
  simp only [initK, State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), h₁.2, h₂.2]

/-- Before the call of the compression function on block `b`. -/
def CA (F S : Addr) (b : Nat) (u : State) : Prop :=
  Lay u F S ∧ u.gpr .rdi = off S oSt ∧ u.gpr .rsi = off S (oY + H.P.B * b) ∧ u.gpr .rdx = 1 ∧ u.gpr .rcx = S ∧
    H.P.B * b + H.P.B ≤ 2048

include hH in
theorem comp_pre {F S : Addr} {b : Nat} {u : State} (h : CA (H := H) F S b u) :
    (compressK hH.md).pre (u.callEntry.withRegions [⟨off S (oY + H.P.B * b), H.P.B * 1⟩]
      [⟨off S oSt, H.P.N⟩, ⟨S, H.P.so⟩]) := by
  obtain ⟨L, hdi, hsi, hdx, hcx, hbB⟩ := h
  have hB := hH.B_le
  have hN := hH.N_le
  have hso := hH.hso
  simp only [compressK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, L.rsp, show (1 : BitVec 64).toNat = 1 from rfl, true_and]
  exact ⟨Offset.disjoint_base S (by unfold oSt; omega) (by unfold oSt; omega),
    Offset.disjoint S (by unfold oY oSt; omega) (by unfold oY; omega) (by unfold oSt; omega),
    Offset.disjoint_base S (by unfold oY; omega) (by unfold oY; omega),
    Region.Disjoint.sub_right L.dRS (Offset.sub_base S (by unfold oSt oRsa; omega)),
    Region.Disjoint.sub_right L.dRS (Region.sub_prefix (by unfold oRsa; omega))⟩

include hH in
theorem comp_cov {F S : Addr} {b : Nat} {u : State} (h : CA (H := H) F S b u) :
    Covers ([⟨off S (oY + H.P.B * b), H.P.B * 1⟩] ++ [⟨off S oSt, H.P.N⟩, ⟨S, H.P.so⟩]) (u.rd ++ u.wr) ∧
      Covers [⟨off S oSt, H.P.N⟩, ⟨S, H.P.so⟩] u.wr := by
  obtain ⟨L, -, -, -, -, hbB⟩ := h
  have hN := hH.N_le
  have hso := hH.hso
  have hS0 : off S 0 = S := BitVec.add_zero S
  have c₁ := L.cov (o := 0) (n := H.P.so) (by unfold oRsa; omega)
  rw [hS0] at c₁
  exact ⟨Covers.right (Covers.append_left (L.cov (by unfold oY oRsa; omega))
    (Covers.pair (L.cov (by unfold oSt oRsa; omega)) c₁)), Covers.pair (L.cov (by unfold oSt oRsa; omega)) c₁⟩

include hH in
theorem comp_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ F S b, CA (H := H) F S b s₁ ∧ CA (H := H) F S b s₂) :
    RelCT isa P (.call H.compN H.compC) fun _ _ => True := by
  refine RelCT.callEx hH.comp.verified hH.comp.ct fun s₁ s₂ hp => ?_
  obtain ⟨F, S, b, h₁, h₂⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, comp_pre hH h₁, comp_pre hH h₂, ?_, (comp_cov hH h₁).1, (comp_cov hH h₁).2,
    (comp_cov hH h₂).1, (comp_cov hH h₂).2, by rw [h₁.1.rsp, h₂.1.rsp]⟩
  obtain ⟨-, a₁, b₁, c₁, d₁, -⟩ := h₁
  obtain ⟨-, a₂, b₂, c₂, d₂, -⟩ := h₂
  simp only [compressK, State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), a₁, a₂, b₁, b₂, c₁, c₂, d₁, d₂, and_self]


/-! ## The pieces -/

/-- The `ne` condition after a count that sets ZF when `j + 1 = n`. -/
theorem eval_ne_cnt {s : State} {j N : Nat} (hj : j < N) (hz : s.zf = some (decide (j + 1 = N))) :
    isa.eval .ne s = some (decide (j + 1 < N)) := by
  simp only [eval, hz, Option.map_some, Option.some.injEq]
  by_cases h : j + 1 = N
  · simp [h]
  · simp only [h, decide_false, Bool.not_false]; exact (decide_eq_true (by omega)).symm

/-- `Pub` after a piece that keeps the regions. -/
theorem Pub.next {F S : Addr} {rest : List Region} {ws ws' : List (Nat × BitVec 64)} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} {t t' : State} (h : Pub F S rest ws rs X t) (L' : Lay t' F S)
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem F S V' W')
    (hw : ∀ p ∈ ws', W' p.1 = p.2) (hx : X' V' W') : Pub F S rest ws' [] X' t' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, fun _ hp => by cases hp⟩

theorem ws_upd {ws : List (Nat × BitVec 64)} {W : Nat → BitVec 64} (hw : ∀ p ∈ ws, W p.1 = p.2) {k : Nat}
    (hk : ∀ p ∈ ws, p.1 ≠ k) (v : BitVec 64) : ∀ p ∈ ws, upd W k v p.1 = p.2 := fun p hp => by
  simp only [upd]; rw [ifn (hk p hp)]; exact hw p hp

theorem hws_w {a : HA} {W : Nat → BitVec 64} (hw : ∀ p ∈ hws a, W p.1 = p.2) :
    W 21 = a.S ∧ W 28 = BitVec.ofNat 64 a.nbm :=
  ⟨hw (21, a.S) (by simp [hws]), hw (28, BitVec.ofNat 64 a.nbm) (by simp [hws])⟩

variable (H) in
/-- After the length field: the index of the last block (secret). -/
def HF (a : HA) (t : State) : Prop :=
  HOk (H := H) n a ∧ Pub a.F a.S a.rest (hws a) [] (fun _ W => ∃ fb, W 30 = BitVec.ofNat 64 fb ∧ fb < a.nbm) t

variable (H) in
/-- Before block `j`. -/
def HL (a : HA) (j : Nat) (t : State) : Prop :=
  HOk (H := H) n a ∧ Pub a.F a.S a.rest (hws a ++ [(29, BitVec.ofNat 64 j)]) []
    (fun _ W => ∃ fb, W 30 = BitVec.ofNat 64 fb ∧ fb < a.nbm) t

variable (H) in
/-- After the blocks. -/
def HD (a : HA) (t : State) : Prop :=
  HOk (H := H) n a ∧ Pub a.F a.S a.rest [(21, a.S)] [] (fun _ _ => True) t

theorem hl_w {a : HA} {j : Nat} {W : Nat → BitVec 64} (hw : ∀ p ∈ hws a ++ [(29, BitVec.ofNat 64 j)], W p.1 = p.2) :
    W 21 = a.S ∧ W 28 = BitVec.ofNat 64 a.nbm ∧ W 29 = BitVec.ofNat 64 j :=
  ⟨hw (21, a.S) (by simp [hws]), hw (28, BitVec.ofNat 64 a.nbm) (by simp [hws]), hw (29, BitVec.ofNat 64 j) (by simp)⟩

theorem mem21 {a : HA} {ws : List (Nat × BitVec 64)} (h : (21, a.S) ∈ ws) : ∀ p ∈ [(21, a.S)], p ∈ ws := by
  intro p hp; rw [List.mem_singleton.mp hp]; exact h

include hH K in
theorem ctInit_ct (hfx : FixedChecks n) : RelCT isa (Two (HE H n)) (ctInit H) (Two (HE H n)) := by
  obtain ⟨_, hs⟩ := hfx.scrSt
  refine two_post (RelCT.seq (two_post (Ψ := fun a t => IA a.F a.S t) (two_pub n [21, 28] [] HA.F HA.S HA.rest hws
      (fun _ => []) (fun a t h => ⟨_, h.2⟩) (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hs)
      fun a t h => ?_) (init_rel hH fun s₁ s₂ ⟨a, h₁, h₂⟩ => ⟨a.F, a.S, h₁, h₂⟩)) fun a t h => ?_
  · have L := h.2.L
    exact WP.mono (scr_ok L (d := .rdi) (by decide) (o := oSt) (by decide)) fun u ⟨hdi, hm, hk⟩ =>
      ⟨L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm]), hdi⟩
  · obtain ⟨V, W, R, hw, hx⟩ := h.2.W
    exact WP.mono (ctInit_ok hH K h.2.L R) fun u ⟨L', _, hwr, _, R', _⟩ => ⟨h.1, h.2.next L' hwr R' hw hx⟩

include hH in
theorem pad80_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (HE H n)) (pad80 H) (Two (HE H n)) := by
  obtain ⟨_, hp⟩ := hc.pad80
  refine two_post (two_pub n [21, 28] [] HA.F HA.S HA.rest hws (fun _ => []) (fun a t h => ⟨_, h.2⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, ℓ, hl, hfit⟩ := h.2.W
  obtain ⟨-, h1, hnb⟩ := h.1
  exact WP.mono (pad80_ok hH h.2.L R hl (hws_w hw).2 h1 hnb (by omega)) fun u P =>
    ⟨h.1, h.2.next P.L P.keep.2.2 P.R hw ⟨ℓ, hl, hfit⟩⟩

include hH in
theorem lenField_ct (hc : HashChecks H.P H.D n) :
    RelCT isa (Two (HE H n)) (.block (lenField H)) (Two (HF H n)) := by
  obtain ⟨_, hp⟩ := hc.lenField
  refine two_post (two_pub n [21] [] HA.F HA.S HA.rest (fun a => [(21, a.S)]) (fun _ => [])
    (fun a t h => ⟨_, h.2.sub (mem21 (by simp [hws])) (fun _ h => h) fun _ _ x => x⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, ℓ, hl, hfit⟩ := h.2.W
  obtain ⟨-, h1, hnb⟩ := h.1
  have hB0 := hH.B_pos
  refine WP.mono (lenField_ok hH h.2.L R hl (by omega)) fun u ⟨L', hk, R'⟩ =>
    ⟨h.1, h.2.next L' hk.2.2 R' (ws_upd hw (by simp [hws]) _) ⟨RsaPss.lastBlk H.P.B H.P.L ℓ, by simp [upd], ?_⟩⟩
  exact (Nat.div_lt_iff_lt_mul hB0).mpr (by omega)

include hH in
theorem lenLoop_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (HF H n)) (lenLoop H) (Two (HF H n)) := by
  obtain ⟨_, hp⟩ := hc.lenLoop
  refine two_post (two_pub n [21, 28] [] HA.F HA.S HA.rest hws (fun _ => []) (fun a t h => ⟨_, h.2⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.W
  obtain ⟨-, -, hnb⟩ := h.1
  exact WP.mono (lenLoop_ok hH h.2.L R (len := (List.range H.P.L).map fun i => V (oLen + i))
    (fun i hi => by simp [List.getD_eq_getElem?_getD, hi]) hf (hws_w hw).2 hfb hnb) fun u O =>
    ⟨h.1, h.2.next O.L O.keep.2.2 O.R hw ⟨fb, hf, hfb⟩⟩

theorem startB_ct (hfx : FixedChecks n) : RelCT isa (Two (HF H n)) (.block [.mov32 .rax (.imm 0), .store (sp sB) .rax])
    (Two fun a t => 0 < a.nbm ∧ HL H n a 0 t) := by
  obtain ⟨_, hp⟩ := hfx.startB
  refine two_post (two_pub n [21, 28] [] HA.F HA.S HA.rest hws (fun _ => []) (fun a t h => ⟨_, h.2⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, hx⟩ := h.2.W
  have L := h.2.L
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem.writeW (off a.F sB) (BitVec.ofNat 64 0))
      ?_ rfl) fun u ⟨hm, hk⟩ => ?_
  · xrun [ea_sp, L.rsp, L.st (d := sB) (by decide)]
    rfl
  have R0 := R.wf L.geo (k := 29) (by decide) (BitVec.ofNat 64 0)
  rw [show off a.F (8 * 29) = off a.F sB from rfl, ← hm] at R0
  refine ⟨h.1.2.1, h.1, L.of_rep' R R0 (by simp [upd]) (hk.gpr (by decide)) hk.2.2, hk.2.2.trans h.2.wr,
    ⟨_, _, R0, fun p hp => ?_, (by obtain ⟨fb, hf, hfb⟩ := hx; exact ⟨fb, by simp [upd, hf], hfb⟩)⟩, fun _ hp => by cases hp⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact ws_upd hw (by simp [hws]) _ p hp
  · rw [List.mem_singleton.mp hp]; simp [upd]


/-- Before block `j`, as the loop sees it. -/
abbrev HB (p : HA × Nat) (t : State) : Prop := p.2 < p.1.nbm ∧ HL H n p.1 p.2 t

theorem hb_bound {p : HA × Nat} {t : State} (h : HB (H := H) n p t) : H.P.B * p.2 + H.P.B ≤ 2048 := by
  obtain ⟨hj, -, -, hnb⟩ := h.1, h.2.1
  rw [← Nat.mul_succ]
  exact Nat.le_trans (Nat.mul_le_mul_left _ hj) (by rw [Nat.mul_comm]; exact hnb)

theorem hb_pub {p : HA × Nat} {t : State} (h : HB (H := H) n p t) :
    Pub p.1.F p.1.S p.1.rest [(21, p.1.S), (29, BitVec.ofNat 64 p.2)] [] (fun _ W => ∃ fb, W 30 = BitVec.ofNat 64 fb ∧ fb < p.1.nbm) t :=
  h.2.2.sub (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp [hws]) (fun _ h => h) fun _ _ x => x

include hH in
theorem compA_ct (hc : HashChecks H.P H.D n) :
    RelCT isa (Two (HB (H := H) n)) (.seq (.block (compArgs H)) (.call H.compN H.compC)) (Two (HB (H := H) n)) := by
  obtain ⟨_, hp⟩ := hc.compArgs
  have hB := hH.B_le
  refine two_post (RelCT.seq (two_post (Ψ := fun p t => CA (H := H) p.1.F p.1.S p.2 t)
    (two_pub n [21, 29] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
      (fun p => [(21, p.1.S), (29, BitVec.ofNat 64 p.2)]) (fun _ => []) (fun p t h => ⟨_, hb_pub n h⟩)
      (fun p t h => h.2.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun p t h => ?_)
    (comp_rel hH fun s₁ s₂ ⟨p, h₁, h₂⟩ => ⟨p.1.F, p.1.S, p.2, h₁, h₂⟩)) fun p t h => ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.2.2.W
    have L := h.2.2.L
    have hbB := hb_bound n h
    have := Nat.le_mul_of_pos_left p.2 hH.B_pos
    exact WP.mono (compArgs_ok hH L R (b := p.2) (by omega) (hl_w hw).2.2) fun u ⟨h1, h2, h3, h4, hm, hk⟩ =>
      ⟨L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm]), h1, h2, h3, h4, hbB⟩
  · obtain ⟨V, W, R, hw, hx⟩ := h.2.2.W
    exact WP.mono (compCall_ok hH h.2.2.L R (hb_bound n h) (hl_w hw).2.2) fun u ⟨L', _, hwr, _, R', _⟩ =>
      ⟨h.1, h.2.1, h.2.2.next L' hwr R' hw hx⟩

include hH in
theorem select_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (HB (H := H) n)) (select H) (Two (HB (H := H) n)) := by
  obtain ⟨_, hp⟩ := hc.select
  refine two_post (two_pub n [21, 29] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
      (fun p => [(21, p.1.S), (29, BitVec.ofNat 64 p.2)]) (fun _ => []) (fun p t h => ⟨_, hb_pub n h⟩)
      (fun p t h => h.2.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun p t h => ?_
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.2.W
  have := Nat.le_trans (Nat.le_mul_of_pos_right _ hH.B_pos) h.2.1.2.2
  exact WP.mono (select_ok hH h.2.2.L R (hl_w hw).2.2 hf (by omega) (by omega)) fun u Sw =>
    ⟨h.1, h.2.1, h.2.2.next Sw.L Sw.keep.2.2 Sw.R hw ⟨fb, hf, hfb⟩⟩

theorem nextB_ct (hfx : FixedChecks n) : RelCT isa (Two (HB (H := H) n)) (.block nextBlock) fun _ _ => True := by
  obtain ⟨_, hp⟩ := hfx.nextB
  exact two_pub n [21, 28, 29] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => hws p.1 ++ [(29, BitVec.ofNat 64 p.2)]) (fun _ => []) (fun p t h => ⟨_, h.2.2⟩)
    (fun p t h => h.2.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp

include hH in
theorem body_wp {a : HA} {j : Nat} {t : State} (hj : j < a.nbm) (h : HL H n a j t) :
    WP isa (seqs [.block (compArgs H), .call H.compN H.compC, select H, .block nextBlock]) t fun t' =>
      isa.eval .ne t' = some (decide (j + 1 < a.nbm)) ∧ (j + 1 < a.nbm → HL H n a (j + 1) t') ∧
      (j + 1 = a.nbm → HD H n a t') := by
  have hbB := hb_bound (H := H) n (p := (a, j)) ⟨hj, h⟩
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.W
  obtain ⟨w21, w28, w29⟩ := hl_w hw
  have hnbm : a.nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right a.nbm hH.B_pos) h.1.2.2
  refine WP.seq_assoc (WP.seq (WP.mono (compCall_ok hH h.2.L R hbB w29)
    fun v ⟨Lv, _, hwrv, _, Rv, _⟩ => ?_))
  refine WP.seq (WP.mono (select_ok hH Lv Rv (b := j) (fb := fb) w29 hf (by omega) (by omega)) fun w Sw => ?_)
  refine WP.mono (nextBlock_ok Sw.L Sw.R (b := j) (nbm := a.nbm) w29 w28 (by omega) (by omega))
    fun u' ⟨hz, Lu', hk', Ru'⟩ => ⟨eval_ne_cnt hj hz, fun _ => ⟨h.1, Lu', hk'.2.2.trans (Sw.keep.2.2.trans
      (hwrv.trans h.2.wr)), ⟨_, _, Ru', fun q hq => ?_, fb, by simp [upd, hf], hfb⟩, fun _ hp => by cases hp⟩,
      fun _ => ⟨h.1, Lu', hk'.2.2.trans (Sw.keep.2.2.trans (hwrv.trans h.2.wr)),
        ⟨_, _, Ru', fun q hq => by rw [List.mem_singleton.mp hq]; simp [upd, w21], trivial⟩, fun _ hp => by cases hp⟩⟩
  rcases List.mem_append.mp hq with hq | hq
  · exact ws_upd (fun q hq => hw q (List.mem_append_left _ hq)) (by simp [hws]) _ q hq
  · rw [List.mem_singleton.mp hq]; simp [upd]

include hH in
theorem compLoop_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (HF H n)) (compLoop H) (Two (HD H n)) := by
  refine RelCT.seq (startB_ct n hfx) (two_loop (Φ := HL H n) HA.nbm ?_ fun a j t hj h => body_wp hH n hj h)
  simp only [seqs]
  exact RelCT.assoc (RelCT.seq (compA_ct hH n hc) (RelCT.seq (select_ct hH n hc) (nextB_ct n hfx)))

theorem digestOut_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (HD H n)) (.block (digestOut H)) fun _ _ => True := by
  obtain ⟨_, hp⟩ := hc.digestOut
  exact two_pub n [21] [] HA.F HA.S HA.rest (fun a => [(21, a.S)]) (fun _ => []) (fun a t h => ⟨_, h.2⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp

include hH K in
/-- `ctHash` is constant time. -/
theorem ctHash_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (HE H n)) (ctHash H) fun _ _ => True := by
  unfold ctHash seqs seqs seqs seqs seqs
  exact (ctInit_ct hH K n hfx).seq ((pad80_ct hH n hc).seq ((lenField_ct hH n hc).seq ((lenLoop_ct hH n hc).seq
    ((compLoop_ct hH n hc hfx).seq (digestOut_ct n hc)))))

end VG.Proof.RsaPss.X86_64
