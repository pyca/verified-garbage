import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain

/-!
# RSA with the CRT on x86-64: constant time of the primes' setup

`wsNew` branches on the prime's length, which is public (`wsNew_ct`).
`primesSetup` (`setup_ct`) runs in the modulus' workspace, then in the
primes'; between its pieces, what the next one reads from the headers
(`SSt`, the primes' links, sizes and bases `WsF`) is kept by the frames of
the pieces before it.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## A new workspace -/

/-- `wsNew`'s first block. -/
def wsB1 (slotWs slotLen : Nat) : List Instr :=
  [.store (hdr slotWs) .rax, .mov .r12 (.mem (hdr slotLen)), .alu .add .r12 (.imm 7), .shift .shr .r12 3,
    .alu .cmp .r12 (.imm 2)]

/-- `wsNew`'s last block. -/
def wsB3 : List Instr :=
  ([.mov .rsi (.reg .rdi), .mov .rdi (.reg .rax), .store (hdr sLink) .rsi, .store (hdr sW) .r12] : List Instr) ++
    setBases ++ ([.mov .rdi (.reg .rsi)] : List Instr)

theorem wsNew_eq (slotWs slotLen : Nat) : wsNew slotWs slotLen =
    [.block (wsB1 slotWs slotLen), .ite .b (.block [.mov32 .r12 (.imm 2)]) (.block []), .block wsB3] := rfl

/-- The public data of `wsNew`: the modulus' working space, the new
workspace's offset and the length. -/
structure WPub where
  B : Addr
  Z : Nat
  o : Nat
  len : Nat

/-- `wsNew_ok`'s hypotheses. -/
def WN (slotWs slotLen : Nat) (p : WPub) (s : State) : Prop :=
  Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ s.gpr .rax = off p.B p.o ∧
    word s.mem p.B (8 * slotLen) = BitVec.ofNat 64 p.len ∧ slotWs < 32 ∧ slotLen < 32 ∧ slotWs ≠ slotLen ∧
    p.len < 2 ^ 32 ∧ 8 * 32 ≤ p.o ∧ p.o + slot (wsWords p.len) 8 ≤ p.Z

/-- After `wsNew`'s first block. -/
def W1 (p : WPub) (t : State) : Prop :=
  t.gpr .rdi = p.B ∧ t.gpr .rax = off p.B p.o ∧ t.gpr .r12 = BitVec.ofNat 64 ((p.len + 7) / 8) ∧
    t.cf = some (decide ((p.len + 7) / 8 < 2))

/-- After `wsNew`'s branch. -/
def W3 (p : WPub) (t : State) : Prop :=
  t.gpr .rdi = p.B ∧ t.gpr .rax = off p.B p.o ∧ t.gpr .r12 = BitVec.ofNat 64 (wsWords p.len)

theorem wsB1_ok {slotWs slotLen : Nat} {p : WPub} {s : State} (h : WN slotWs slotLen p s) :
    WP isa (.block (wsB1 slotWs slotLen)) s (W1 p) := by
  obtain ⟨hs, hdi, hax, hlen, hws, hsl, hne, hlen', ho, hZ⟩ := h
  have hn := hs.nowrap
  have h256 : 256 ≤ slot (wsWords p.len) 8 := by unfold slot hdrBytes; omega
  have hX : ∀ v : BitVec 64, (s.mem.writeW (off p.B (8 * slotWs)) v).readW (off p.B (8 * slotLen)) 64 =
      BitVec.ofNat 64 p.len := fun v => (hdrStore_hdr s.mem p.B v hws hsl hne).trans hlen
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 ((p.len + 7) / 8) ∧
      t.cf = some (decide ((p.len + 7) / 8 < 2)))
    (by
      unfold wsB1
      xrun [State.ea, hdr, hdi, hdrOff, hs.st (d := 8 * slotWs) (by omega), hax,
        hs.ld (d := 8 * slotLen) (by omega), hX, shr3_w p.len hlen', sx2,
        cf_lt2 (show (p.len + 7) / 8 < 2 ^ 64 by omega)]) rfl)
    fun t ⟨⟨h12, hcf⟩, k⟩ => ⟨(k.gpr (by decide)).trans hdi, (k.gpr (by decide)).trans hax, h12, hcf⟩

theorem pins_w3 : Pins W3 [.rdi, .rax, .r12] :=
  pins_of (fun p r => if r = .rdi then p.B else if r = .rax then off p.B p.o else
      BitVec.ofNat 64 (wsWords p.len)) fun p s h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2

theorem pins_nil {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr (by simp)

/-- `wsNew`, given that the taint analysis checks its first block. -/
theorem wsNew_ct {slotWs slotLen : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h1 : (taint.check (Taint.ofRegs [.rdi]) (.block (wsB1 slotWs slotLen)) hc).isSome = true) :
    RelCT isa (Two (WN slotWs slotLen)) (seqs (wsNew slotWs slotLen)) fun _ _ => True := by
  rw [wsNew_eq]
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := W1) [.rdi] (pins_of (fun p _ => p.B) fun p s h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.2.1) h1 fun p s h => wsB1_ok h) ?_
  refine RelCT.seq (two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2.2.2, h₂.2.2.2]) ?_ ?_)
    (two_taint _ pins_w3 (by taint_decide))
  · refine two_piece (Ψ := W3) [] pins_nil (by taint_decide) fun p s ⟨h, hb⟩ => ?_
    have h2 : (p.len + 7) / 8 < 2 := by
      simp only [eval, h.2.2.2, Option.some.injEq, decide_eq_true_eq] at hb; exact hb
    refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (wsWords p.len)) (by
      xrun
      unfold wsWords; rw [Nat.max_eq_left (by omega)]; rfl) rfl)
      fun t ⟨h12, k⟩ => ⟨(k.gpr (by decide)).trans h.1, (k.gpr (by decide)).trans h.2.1, h12⟩
  · refine two_piece (Ψ := W3) [] pins_nil (by taint_decide) fun p s ⟨h, hb⟩ => ?_
    have h2 : ¬ (p.len + 7) / 8 < 2 := by
      simp only [eval, h.2.2.2, Option.some.injEq, decide_eq_false_iff_not] at hb; exact hb
    refine WP.block_nil ⟨h.1, h.2.1, ?_⟩
    rw [h.2.2.1]; unfold wsWords; rw [Nat.max_eq_right (by omega)]

/-! ## The setup's states -/

/-- What the setup keeps: the modulus' working space and header, its
arguments, and the byte strings. -/
def SSt (p : SetupPub) (t : State) : Prop :=
  ∃ pb qb ib : List Byte, Scr t p.B p.Z ∧ Hdr t.mem p.B p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    offQ p.w p.pl + slot (wsWords p.ql) 8 ≤ p.Z ∧
    word t.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl ∧ word t.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql ∧
    word t.mem p.B (8 * sP) = p.pp ∧ word t.mem p.B (8 * sQ) = p.qp ∧ word t.mem p.B (8 * sQinv) = p.ip ∧
    Src t p.B p.Z p.pp pb ∧ Src t p.B p.Z p.qp qb ∧ Src t p.B p.Z p.ip ib ∧ pb.length = p.pl ∧
    qb.length = p.ql ∧ ib.length = p.pl ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w

theorem SSt.frm {p : SetupPub} {t t' : State} (h : SSt p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (hr : ∀ r ∈ rs, 8 * 29 ≤ r.1 ∧ r.1 + r.2 ≤ p.Z) {regs : List Reg} (k : Keep regs t t') : SSt p t' := by
  obtain ⟨pb, qb, ib, hs, hH, a1, a2, hZ, b1, b2, b3, b4, b5, c1, c2, c3, d⟩ := h
  have hn := hs.nowrap
  have h8 : 256 ≤ offQ p.w p.pl := by unfold offQ slot hdrBytes; omega
  have hw : ∀ i < 29, word t'.mem p.B (8 * i) = word t.mem p.B (8 * i) := fun i hi =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega)) (by omega)
  have hi := InScr.of_frm hf fun r hr' => (hr r hr').2
  exact ⟨pb, qb, ib, hs.congr k.2.2, ⟨(hw _ (by decide)).trans hH.hw, (hw _ (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩, a1, a2, hZ, (hw _ (by decide)).trans b1,
    (hw _ (by decide)).trans b2, (hw _ (by decide)).trans b3, (hw _ (by decide)).trans b4,
    (hw _ (by decide)).trans b5, c1.congrK hi k, c2.congrK hi k, c3.congrK hi k, d⟩

theorem SSt.mem {p : SetupPub} {t t' : State} (h : SSt p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : Keep regs t t') : SSt p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k

theorem SSt.nowrap {p : SetupPub} {t : State} (h : SSt p t) : p.B.toNat + p.Z ≤ 2 ^ 64 :=
  let ⟨_, _, _, hs, _⟩ := h; hs.nowrap

theorem SSt.scr {p : SetupPub} {t : State} (h : SSt p t) : Scr t p.B p.Z :=
  let ⟨_, _, _, hs, _⟩ := h; hs

theorem SSt.bounds {p : SetupPub} {t : State} (h : SSt p t) :
    8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ offQ p.w p.pl + slot (wsWords p.ql) 8 ≤ p.Z ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧
      1 ≤ p.ql ∧ p.ql < 8 * p.w :=
  let ⟨_, _, _, _, _, a1, a2, hZ, _, _, _, _, _, _, _, _, _, _, _, d1, d2, d3, d4⟩ := h
  ⟨a1, a2, hZ, d1, d2, d3, d4⟩

/-- A prime's workspace at `off B o`: its link, size and bases. -/
def WsF (m : Mem) (B : Addr) (o wx : Nat) : Prop :=
  word m (off B o) (8 * sLink) = B ∧ word m (off B o) (8 * sW) = BitVec.ofNat 64 wx ∧
    ∀ j < 8, word m (off B o) (8 * sArr j) = off (off B o) (slot wx j)

theorem WsF.frm {m m' : Mem} {B : Addr} {o wx : Nat} (h : WsF m B o wx) {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, o + 8 * 17 ≤ r.1 ∨ r.1 + r.2 ≤ o) (ho : o + 8 * 17 ≤ 2 ^ 64) : WsF m' B o wx := by
  have hw : ∀ i < 17, word m' (off B o) (8 * i) = word m (off B o) (8 * i) := fun i hi => by
    rw [word_off, word_off]
    exact hf.word_eq (fun r hr' => by have := hr r hr'; omega) (by omega)
  exact ⟨(hw _ (by decide)).trans h.1, (hw _ (by decide)).trans h.2.1,
    fun j hj => (hw _ (by unfold sArr; omega)).trans (h.2.2 j hj)⟩

/-- After `p`'s workspace. -/
def SA (p : SetupPub) (t : State) : Prop :=
  SSt p t ∧ word t.mem p.B (8 * sWsP) = off p.B (offP p.w) ∧ WsF t.mem p.B (offP p.w) (wsWords p.pl)

/-- After `q`'s workspace. -/
def SB (p : SetupPub) (t : State) : Prop :=
  SA p t ∧ word t.mem p.B (8 * sWsQ) = off p.B (offQ p.w p.pl) ∧ WsF t.mem p.B (offQ p.w p.pl) (wsWords p.ql)

theorem SB.frm {p : SetupPub} {t t' : State} (h : SB p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (hr : ∀ r ∈ rs, offP p.w + 8 * 17 ≤ r.1 ∧ (r.1 + r.2 ≤ offQ p.w p.pl ∨ offQ p.w p.pl + 8 * 17 ≤ r.1) ∧
      r.1 + r.2 ≤ p.Z) {regs : List Reg} (k : Keep regs t t') : SB p t' := by
  obtain ⟨⟨hS, hP, hFP⟩, hQ, hFQ⟩ := h
  have hn := hS.nowrap
  obtain ⟨a1, -, hZ, -, -, -, -⟩ := hS.bounds
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  have hPQ : offP p.w + 256 ≤ offQ p.w p.pl := by unfold offP offQ slot hdrBytes; omega
  have hP0 : offP p.w = slot p.w 8 := rfl
  have hQZ : offQ p.w p.pl + 256 ≤ p.Z := by unfold slot hdrBytes at hZ; omega
  refine ⟨⟨hS.frm hf (fun r hr' => by have := hr r hr'; omega) k, ?_, hFP.frm hf (fun r hr' => by
    have := hr r hr'; omega) (by omega)⟩, ?_, hFQ.frm hf (fun r hr' => by have := hr r hr'; omega) (by omega)⟩
  · rw [hf.word_eq (fun r hr' => by have := hr r hr'; unfold sWsP sFn; omega) (by unfold sWsP sFn; omega)]
    exact hP
  · rw [hf.word_eq (fun r hr' => by have := hr r hr'; unfold sWsQ sFn; omega) (by unfold sWsQ sFn; omega)]
    exact hQ

theorem SA.frm' {p : SetupPub} {t t' : State} (h : SA p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : Keep regs t t') : SA p t' :=
  ⟨h.1.mem hm k, hm ▸ h.2.1, hm ▸ h.2.2⟩

/-- `SB` with `rdi` at `f p`. -/
def SBr (f : SetupPub → Addr) (p : SetupPub) (t : State) : Prop := SB p t ∧ t.gpr .rdi = f p

theorem pins_sbr (f : SetupPub → Addr) : Pins (SBr f) [.rdi] :=
  pins_of (fun p _ => f p) fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2

theorem SetupPre.sst {p : SetupPub} {s : State} (h : SetupPre p s) : SSt p s ∧ s.gpr .rdi = p.B :=
  let ⟨pb, qb, ib, hg, a1, a2, hZ, b1, b2, b3, b4, b5, c1, c2, c3, d⟩ := h
  ⟨⟨pb, qb, ib, hg.scr, hg.hdr, a1, a2, hZ, b1, b2, b3, b4, b5, c1, c2, c3, d⟩, hg.rdi⟩

/-- Before `p`'s workspace: its offset in `rax`. -/
def SS1 (p : SetupPub) (t : State) : Prop := SSt p t ∧ t.gpr .rdi = p.B ∧ t.gpr .rax = off p.B (offP p.w)

/-- Before `q`'s workspace: its offset in `rax`. -/
def SS3 (p : SetupPub) (t : State) : Prop := SA p t ∧ t.gpr .rdi = p.B ∧ t.gpr .rax = off p.B (offQ p.w p.pl)

theorem stage1_ok {p : SetupPub} {s : State} (h : SetupPre p s) :
    WP isa (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ wsEnd)) s (SS1 p) := by
  obtain ⟨hS, hdi⟩ := h.sst
  have hS' := hS
  obtain ⟨_, _, _, hs, hH, a1, -, hZ, -⟩ := hS'
  have : slot p.w 8 ≤ offQ p.w p.pl := by unfold offQ; omega
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = p.B ∧ t.mem = s.mem) (by xrun [hdi]) rfl)
    fun s₁ ⟨⟨hdx₁, hm₁⟩, k₁⟩ => ?_
  exact WP.mono (wsEnd_ok (wx := p.w) (hs.congr k₁.2.2) hdx₁ (by rw [hm₁]; exact hH.hw)
    (by rw [hm₁]; exact hH.harr _ (by decide)) (by omega)) fun t ⟨hax, hm₂, k₂⟩ =>
    ⟨hS.mem (hm₂.trans hm₁) (k₁.trans k₂), (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi), hax⟩

theorem SB.mem {p : SetupPub} {t t' : State} (h : SB p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : Keep regs t t') : SB p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k

theorem wsP_ok {p : SetupPub} {s : State} (h : SS1 p s) :
    WP isa (seqs (wsNew sWsP sPlen)) s fun t => SA p t ∧ t.gpr .rdi = p.B := by
  obtain ⟨hS, hdi, hax⟩ := h
  have hS' := hS
  obtain ⟨_, _, _, hs, -, a1, a2, hZ, hpl, -, -, -, -, -, -, -, -, -, -, d1, d2, -, -⟩ := hS'
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  unfold offQ at hZ
  exact WP.mono (wsNew_ok (o := offP p.w) (len := p.pl) hs hdi hax (by decide) (by decide) (by decide) hpl
    (by omega) (by unfold offP; omega) (by unfold offP; omega))
    fun t ⟨hWs, hl, hw, ha, hdi', f, k⟩ => ⟨⟨hS.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsP, sFn, offP] <;> omega) k, hWs, hl, hw, ha⟩, hdi'⟩

/-- `q`'s workspace's base: `p`'s end. -/
def SS2 (p : SetupPub) (t : State) : Prop :=
  SA p t ∧ t.gpr .rdi = p.B ∧ t.gpr .rdx = off p.B (offP p.w)

theorem stage2_ok {p : SetupPub} {s : State} (h : SA p s ∧ s.gpr .rdi = p.B) :
    WP isa (.block [.mov .rdx (.mem (hdr sWsP))]) s (SS2 p) := by
  obtain ⟨hA, hdi⟩ := h
  have hs := hA.1.scr
  have hWsP := hA.2.1
  have := hA.1.bounds
  have hn := hs.nowrap
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  unfold offQ at this
  exact WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = off p.B (offP p.w) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hWsP]) rfl)
    fun t ⟨⟨hdx, hm⟩, k⟩ => ⟨hA.frm' hm k, (k.gpr (by decide)).trans hdi, hdx⟩

theorem stage3_ok {p : SetupPub} {s : State} (h : SS2 p s) : WP isa (.block wsEnd) s (SS3 p) := by
  obtain ⟨hA, hdi, hdx⟩ := h
  have hA' := hA
  obtain ⟨⟨_, _, _, hs, -, a1, -, hZ, -⟩, -, -, hw, ha⟩ := hA'
  have hn := hs.nowrap
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  unfold offQ at hZ
  refine WP.mono (wsEnd_ok (wx := wsWords p.pl) (hs.sub (o := offP p.w)
    (n := slot (wsWords p.pl) 8) (by unfold offP; omega) (by omega)) hdx hw
    (ha _ (by decide)) (Nat.le_refl _)) fun t ⟨hax, hm, k⟩ => ?_
  rw [off_off] at hax
  exact ⟨hA.frm' hm k, (k.gpr (by decide)).trans hdi, hax⟩

theorem wsQ_ok {p : SetupPub} {s : State} (h : SS3 p s) :
    WP isa (seqs (wsNew sWsQ sQlen)) s (SBr (·.B) p) := by
  obtain ⟨hA, hdi, hax⟩ := h
  have hA' := hA
  obtain ⟨⟨_, _, _, hs, -, a1, a2, hZ, -, hql, -, -, -, -, -, -, -, -, -, d1, d2, d3, d4⟩, hWsP, hF⟩ := hA'
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega
  have hn := hs.nowrap
  unfold offQ at hZ
  refine WP.mono (wsNew_ok (o := offQ p.w p.pl) (len := p.ql) hs hdi hax (by decide) (by decide) (by decide) hql
    (by omega) (by unfold offQ; omega) (by unfold offQ; omega))
    fun t ⟨hWs, hl, hw, ha, hdi', f, k⟩ => ⟨⟨⟨hA.1.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsQ, sFn, offQ] <;> omega) k, ?_, hF.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsQ, sFn, offQ, offP] <;> omega) (by unfold offP; omega)⟩,
      hWs, hl, hw, ha⟩, hdi'⟩
  rw [f.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sWsQ, sWsP, sFn, offQ] <;> omega) (by unfold sWsP sFn; omega)]
  exact hWsP

theorem SB.scr {p : SetupPub} {t : State} (h : SB p t) : Scr t p.B p.Z := let ⟨⟨⟨_, _, _, hs, _⟩, _⟩, _⟩ := h; hs

theorem SB.bounds {p : SetupPub} {t : State} (h : SB p t) :
    8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ offQ p.w p.pl + slot (wsWords p.ql) 8 ≤ p.Z ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧
      1 ≤ p.ql ∧ p.ql < 8 * p.w := h.1.1.bounds

/-- Into a workspace from the modulus' (`enterP`, `enterQ`), or back (`leave`). -/
theorem SB.move {p : SetupPub} {s : State} (h : SB p s) {X : Addr} {i : Nat} {A' : Addr}
    (hdi : s.gpr .rdi = X) (hl : InRegions (s.rd ++ s.wr) (off X (8 * i)) 8) (hw : word s.mem X (8 * i) = A') :
    WP isa (.block [.mov .rdi (.mem (hdr i))]) s (SBr (fun _ => A') p) :=
  WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = A' ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl, hw]) rfl) fun t ⟨⟨hdi', hm⟩, k⟩ => ⟨h.mem hm k, hdi'⟩

/-- A prime's workspace context from `SB`. -/
theorem SB.sub {p : SetupPub} {s : State} (h : SB p s) {o wx : Nat} (hdi : s.gpr .rdi = off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o) (hhi : o + slot wx 8 ≤ p.Z) :
    SubCtx s p.B p.Z o p.w wx (word s.mem (off p.B o) (8 * sMinv)) :=
  let ⟨⟨⟨_, _, _, hs, hH, _⟩, _⟩, _⟩ := h
  ⟨hs, hdi, hdr_any hF.2.1 hF.2.2, hF.1, hH.hw, hH.harr, hlo, hhi⟩

/-- A load into a prime's workspace keeps `SB`. -/
theorem SB.load {p : SetupPub} {s : State} {o wx j sp sl len : Nat} {ptr : Addr} (h : SB p s)
    (hL : LPre j sp sl ⟨⟨p.B, p.Z, o, p.w, wx⟩, ptr, len⟩ s)
    (hr : offP p.w + 8 * 17 ≤ o + 256 ∧ (o + slot wx 8 ≤ offQ p.w p.pl ∨ offQ p.w p.pl + 8 * 17 ≤ o + 256)) :
    WP isa (seqs (loadArr j sp sl)) s fun t => SB p t ∧ t.gpr .rdi = off p.B o := by
  simp only [LPre] at hL
  obtain ⟨minv, bs, hc, hw2, hwx, hw30, hj, hsp, hsl, hp, hl, hbl, hsrc, hk1, hk', hkw⟩ := hL
  have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hc.scr.nowrap
  have hi : o + slot wx 8 ≤ p.Z := hc.hi
  have h8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  exact WP.mono (primeLoad_ok hc hw2 hwx hw30 hj hsp hsl hp hl hsrc hk1 hk' hkw) fun t ⟨hc', _, ho, k⟩ =>
    ⟨h.frm (Frm.of_load ho hj (by omega) (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; simp only; omega) k, hc'.rdi⟩

/-- `LPre` from `SB`, in the workspace at `off B o` (`rdi`). -/
theorem SB.lpre {p : SetupPub} {s : State} (h : SB p s) {o wx j sp sl len : Nat} {ptr : Addr} {bs : List Byte}
    (hdi : s.gpr .rdi = off p.B o) (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o) (hhi : o + slot wx 8 ≤ p.Z)
    (hw2 : 2 ≤ wx) (hwx : wx ≤ p.w) (hj : j < 8) (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem p.B (8 * sp) = ptr) (hl : word s.mem p.B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hbl : bs.length = len) (hsrc : Src s p.B p.Z ptr bs) (hk1 : 1 ≤ bs.length) (hk' : bs.length < 2 ^ 31)
    (hkw : (bs.length + 7) / 8 ≤ wx) : LPre j sp sl ⟨⟨p.B, p.Z, o, p.w, wx⟩, ptr, len⟩ s :=
  ⟨_, bs, h.sub hdi hF hlo hhi, hw2, hwx, by have := h.bounds; show p.w < 2 ^ 30; omega, hj, hsp, hsl, hp, hl, hbl, hsrc, hk1, hk',
    hkw⟩

theorem lpreP {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offP p.w)) p s) :
    LPre Public.aN sP sPlen ⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.pp, p.pl⟩ s ∧
      LPre aChunk sQinv sPlen ⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.ip, p.pl⟩ s := by
  obtain ⟨hB, hdi⟩ := h
  have hB' := hB
  obtain ⟨⟨⟨pb, qb, ib, hs, -, a1, a2, hZ, hpl, -, hpp, -, hip, c1, -, c3, l1, -, l3, d1, d2, -, -⟩, -, hF⟩, -⟩ := hB'
  unfold offQ at hZ
  have hw := wsWords_le d2 (by omega)
  exact ⟨hB.lpre hdi hF (Nat.le_refl _) (by unfold offP; omega) (by unfold wsWords; omega) hw (by decide)
    (by decide) (by decide) hpp (by rw [l1]; exact hpl) l1 c1 (by omega) (by omega) (by unfold wsWords; omega),
    hB.lpre hdi hF (Nat.le_refl _) (by unfold offP; omega) (by unfold wsWords; omega) hw (by decide)
    (by decide) (by decide) hip (by rw [l3]; exact hpl) l3 c3 (by omega) (by omega) (by unfold wsWords; omega)⟩

theorem lpreQ {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offQ p.w p.pl)) p s) :
    LPre Public.aN sQ sQlen ⟨⟨p.B, p.Z, offQ p.w p.pl, p.w, wsWords p.ql⟩, p.qp, p.ql⟩ s := by
  obtain ⟨hB, hdi⟩ := h
  have hB' := hB
  obtain ⟨⟨⟨pb, qb, ib, hs, -, a1, a2, hZ, -, hql, -, hqp, -, -, c2, -, -, l2, -, -, -, d3, d4⟩, -, -⟩, -, hF⟩ := hB'
  exact hB.lpre hdi hF (by unfold offQ; omega) hZ (by unfold wsWords; omega) (wsWords_le d4 (by omega))
    (by decide) (by decide) (by decide) hqp (by rw [l2]; exact hql) l2 c2 (by omega) (by omega)
    (by unfold wsWords; omega)

theorem SS1.wn {p : SetupPub} {s : State} (h : SS1 p s) :
    WN sWsP sPlen ⟨p.B, p.Z, offP p.w, p.pl⟩ s := by
  obtain ⟨⟨_, _, _, hs, -, a1, a2, hZ, hpl, -, -, -, -, -, -, -, -, -, -, d1, d2, -, -⟩, hdi, hax⟩ := h
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  unfold offQ at hZ
  exact ⟨hs, hdi, hax, hpl, by decide, by decide, by decide, by simp only; omega, by simp only; unfold offP; omega,
    by simp only; unfold offP; omega⟩

theorem SS3.wn {p : SetupPub} {s : State} (h : SS3 p s) :
    WN sWsQ sQlen ⟨p.B, p.Z, offQ p.w p.pl, p.ql⟩ s := by
  obtain ⟨⟨⟨_, _, _, hs, -, a1, a2, hZ, -, hql, -, -, -, -, -, -, -, -, -, -, -, d3, d4⟩, -⟩, hdi, hax⟩ := h
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  exact ⟨hs, hdi, hax, hql, by decide, by decide, by decide, by simp only; omega, by simp only; unfold offQ; omega,
    by simp only; omega⟩

theorem enterP_ok {p : SetupPub} {s : State} (h : SBr (·.B) p s) :
    WP isa (.block [enterP]) s (SBr (fun p => off p.B (offP p.w)) p) := by
  obtain ⟨h, hdi⟩ := h
  have := h.bounds
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  exact h.move (X := p.B) (i := sWsP) hdi (h.scr.ld (by unfold sWsP sFn offQ at *; omega)) h.1.2.1

theorem leaveP_ok {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offP p.w)) p s) :
    WP isa (.block [leave]) s (SBr (·.B) p) := by
  obtain ⟨h, hdi⟩ := h
  have hF := h.1.2.2
  have := h.bounds
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  exact h.move (X := off p.B (offP p.w)) (i := sLink) hdi ((h.scr.sub (o := offP p.w)
    (n := slot (wsWords p.pl) 8) (by unfold offQ offP at *; omega) (by omega)).ld (by unfold sLink sFn; omega)) hF.1

theorem enterQ_ok {p : SetupPub} {s : State} (h : SBr (·.B) p s) :
    WP isa (.block [enterQ]) s (SBr (fun p => off p.B (offQ p.w p.pl)) p) := by
  obtain ⟨h, hdi⟩ := h
  have := h.bounds
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  exact h.move (X := p.B) (i := sWsQ) hdi (h.scr.ld (by unfold sWsQ sFn offQ at *; omega)) h.2.1

theorem loadP1_ok {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offP p.w)) p s) :
    WP isa (seqs (loadArr Public.aN sP sPlen)) s (SBr (fun p => off p.B (offP p.w)) p) :=
  SB.load (o := offP p.w) (wx := wsWords p.pl) h.1 (lpreP h).1
    ⟨by omega, Or.inl (by unfold offQ offP; omega)⟩

theorem loadP2_ok {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offP p.w)) p s) :
    WP isa (seqs (loadArr aChunk sQinv sPlen)) s (SBr (fun p => off p.B (offP p.w)) p) :=
  SB.load (o := offP p.w) (wx := wsWords p.pl) h.1 (lpreP h).2
    ⟨by omega, Or.inl (by unfold offQ offP; omega)⟩

theorem loadQ_ok {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offQ p.w p.pl)) p s) :
    WP isa (seqs (loadArr Public.aN sQ sQlen)) s (SBr (fun p => off p.B (offQ p.w p.pl)) p) :=
  SB.load (o := offQ p.w p.pl) (wx := wsWords p.ql) h.1 (lpreQ h) ⟨by unfold offQ offP; omega, Or.inr (by omega)⟩

theorem leaveEnterQ_ct : RelCT isa (Two (SBr fun p => off p.B (offP p.w))) (.block [leave, enterQ])
    (Two (SBr fun p => off p.B (offQ p.w p.pl))) :=
  RelCT.block_append (l₁ := ([leave] : List Instr))
    (RelCT.seq (two_piece (Ψ := SBr (·.B)) [.rdi] (pins_sbr _) (by taint_decide) fun p s h => leaveP_ok h)
      (two_piece [.rdi] (pins_sbr _) (by taint_decide) fun p s h => enterQ_ok h))

theorem setup_ct : SetupCT := by
  unfold SetupCT primesSetup
  simp only [List.append_assoc]
  -- `p`'s workspace.
  refine RelCT.seqs_append (by simp) (by simp [wsNew]) (RelCT.seq (two_piece (Ψ := SS1) [.rdi]
    (pins_of (fun p _ => p.B) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.sst.2) (by taint_decide)
    fun p s h => stage1_ok h) ?_)
  refine RelCT.seqs_append (by simp [wsNew]) (by simp) (RelCT.seq (two_post (two_map
    (fun p : SetupPub => (⟨p.B, p.Z, offP p.w, p.pl⟩ : WPub)) (fun p s h => h.wn) (wsNew_ct (by taint_decide)))
    fun p s h => wsP_ok h) ?_)
  -- `q`'s workspace.
  refine RelCT.seqs_append (by simp) (by simp [wsNew]) (RelCT.seq (RelCT.block_append
    (l₁ := ([.mov .rdx (.mem (hdr sWsP))] : List Instr)) (RelCT.seq (two_piece (Ψ := SS2) [.rdi]
    (pins_of (fun p _ => p.B) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2) (by taint_decide)
    fun p s h => stage2_ok h) (two_piece (Ψ := SS3) [.rdx]
    (pins_of (fun p _ => off p.B (offP p.w)) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2) (by taint_decide)
    fun p s h => stage3_ok h))) ?_)
  refine RelCT.seqs_append (by simp [wsNew]) (by simp) (RelCT.seq (two_post (two_map
    (fun p : SetupPub => (⟨p.B, p.Z, offQ p.w p.pl, p.ql⟩ : WPub)) (fun p s h => h.wn) (wsNew_ct (by taint_decide)))
    fun p s h => wsQ_ok h) ?_)
  -- Into `p`'s workspace: `p` and `qInv`.
  refine RelCT.seqs_append (by simp) (by simp [loadArr]) (RelCT.seq (two_piece
    (Ψ := SBr fun p => off p.B (offP p.w)) [.rdi] (pins_sbr _) (by taint_decide) fun p s h => enterP_ok h) ?_)
  refine RelCT.seqs_append (by simp [loadArr]) (by simp [loadArr]) (RelCT.seq (two_post (Ψ := SBr fun p => off p.B (offP p.w)) (two_map
    (fun p : SetupPub => (⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.pp, p.pl⟩ : BPub)) (fun p s h => (lpreP h).1)
    loadArr_ct_pN) fun p s h => loadP1_ok h) ?_)
  refine RelCT.seqs_append (by simp [loadArr]) (by simp) (RelCT.seq (two_post (Ψ := SBr fun p => off p.B (offP p.w)) (two_map
    (fun p : SetupPub => (⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.ip, p.pl⟩ : BPub)) (fun p s h => (lpreP h).2)
    loadArr_ct_pI) fun p s h => loadP2_ok h) ?_)
  -- Into `q`'s workspace: `q`.
  refine RelCT.seqs_append (by simp) (by simp [loadArr]) (RelCT.seq leaveEnterQ_ct ?_)
  refine RelCT.seqs_append (by simp [loadArr]) (by simp) (RelCT.seq (two_post (Ψ := SBr fun p => off p.B (offQ p.w p.pl)) (two_map
    (fun p : SetupPub => (⟨⟨p.B, p.Z, offQ p.w p.pl, p.w, wsWords p.ql⟩, p.qp, p.ql⟩ : BPub))
    (fun p s h => lpreQ h) loadArr_ct_qN)
    fun p s h => loadQ_ok h) ?_)
  exact two_taint [.rdi] (pins_sbr _) (by taint_decide)

end VG.Proof.Bignum.X86_64
