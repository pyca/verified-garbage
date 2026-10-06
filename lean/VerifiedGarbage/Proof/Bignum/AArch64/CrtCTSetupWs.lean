import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad

/-!
# RSA with the CRT on AArch64: constant time of the primes' setup

`wsNew` computes the prime's size without branching (a `csel`), so the
taint analysis checks it from its bases. `primesSetup` (`setup_ct`) runs in
the modulus' workspace, then in the primes'; between its pieces, what the
next one reads from the headers (`SSt`, the primes' links, sizes and bases
`WsF`) is kept by the frames of the pieces before it.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## The setup's states -/

/-- What the setup keeps: the modulus' working space and header, its
arguments, and the byte strings. -/
def SSt (p : SetupPub) (t : State) : Prop :=
  ∃ pb qb ib : List Byte, Scr t p.B p.Z ∧ Hdr t.mem p.B p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    offQ p.w p.pl + slot (wsWords p.ql) 8 + tabBytes (wsWords p.ql) ≤ p.Z ∧
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
  exact ⟨pb, qb, ib, hs.congr k.wr, ⟨(hw _ (by decide)).trans hH.hw, (hw _ (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩, a1, a2, hZ, (hw _ (by decide)).trans b1,
    (hw _ (by decide)).trans b2, (hw _ (by decide)).trans b3, (hw _ (by decide)).trans b4,
    (hw _ (by decide)).trans b5, c1.congrK hi k, c2.congrK hi k, c3.congrK hi k, d⟩

theorem SSt.mem {p : SetupPub} {t t' : State} (h : SSt p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : Keep regs t t') : SSt p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k

theorem SSt.scr {p : SetupPub} {t : State} (h : SSt p t) : Scr t p.B p.Z :=
  let ⟨_, _, _, hs, _⟩ := h; hs

theorem SSt.bounds {p : SetupPub} {t : State} (h : SSt p t) :
    8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ offQ p.w p.pl + slot (wsWords p.ql) 8 + tabBytes (wsWords p.ql) ≤ p.Z ∧ 1 ≤ p.pl ∧
      p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w :=
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
  have hn := hS.scr.nowrap
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

theorem SB.mem {p : SetupPub} {t t' : State} (h : SB p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : Keep regs t t') : SB p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k

theorem SB.scr {p : SetupPub} {t : State} (h : SB p t) : Scr t p.B p.Z := h.1.1.scr

theorem SB.bounds {p : SetupPub} {t : State} (h : SB p t) :
    8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ offQ p.w p.pl + slot (wsWords p.ql) 8 + tabBytes (wsWords p.ql) ≤ p.Z ∧ 1 ≤ p.pl ∧
      p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w := h.1.1.bounds

/-- `SB` with `x0` at `f p`. -/
def SBr (f : SetupPub → Addr) (p : SetupPub) (t : State) : Prop := SB p t ∧ t.gpr .x0 = f p

theorem pins_sbr (f : SetupPub → Addr) : Pins (SBr f) [.x0] :=
  pins_of (fun p _ => f p) fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2

theorem SetupPre.sst {p : SetupPub} {s : State} (h : SetupPre p s) : SSt p s ∧ s.gpr .x0 = p.B :=
  let ⟨pb, qb, ib, hg, a1, a2, hZ, b1, b2, b3, b4, b5, c1, c2, c3, d⟩ := h
  ⟨⟨pb, qb, ib, hg.scr, hg.hdr, a1, a2, hZ, b1, b2, b3, b4, b5, c1, c2, c3, d⟩, hg.x0⟩

/-! ## The workspaces -/

/-- Before `p`'s workspace: its base in `x4`. -/
def SS1 (p : SetupPub) (t : State) : Prop := SSt p t ∧ t.gpr .x0 = p.B ∧ t.gpr .x4 = off p.B (offP p.w)

/-- Before `q`'s workspace: its base in `x4`. -/
def SS3 (p : SetupPub) (t : State) : Prop := SA p t ∧ t.gpr .x0 = p.B ∧ t.gpr .x4 = off p.B (offQ p.w p.pl)

theorem pins_ws {Φ : SetupPub → State → Prop} (f : SetupPub → Addr)
    (h : ∀ p s, Φ p s → s.gpr .x0 = p.B ∧ s.gpr .x4 = f p) : Pins Φ [.x0, .x4] :=
  pins_of (fun p r => if r = .x0 then p.B else f p) fun p s hs r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (h p s hs).1
    · exact (h p s hs).2

theorem stage1_ok {p : SetupPub} {s : State} (h : SetupPre p s) :
    WP isa (.block (([mov .x5 .x0] : List Instr) ++ wsEnd)) s (SS1 p) := by
  obtain ⟨hS, h0⟩ := h.sst
  have hS' := hS
  obtain ⟨_, _, _, hs, hH, a1, a2, hZ, -⟩ := hS'
  have : slot p.w 8 ≤ offQ p.w p.pl := by unfold offQ; omega
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.B ∧ t.mem = s.mem) (by brun [h0])
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h5₁, hm₁⟩, k₁⟩ => ?_
  exact WP.mono (wsEnd_ok (wx := p.w) (hs.congr k₁.wr) h5₁ (by rw [hm₁]; exact hH.hw) (by omega)
    (by rw [hm₁]; exact hH.harr _ (by decide)) (by omega)) fun t ⟨⟨h4, _, hm₂⟩, k₂⟩ =>
    ⟨hS.mem (hm₂.trans hm₁) (k₁.trans k₂), (k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans h0), h4⟩

theorem wsP_ok {p : SetupPub} {s : State} (h : SS1 p s) :
    WP isa (.block (wsNew sWsP sPlen)) s fun t => SA p t ∧ t.gpr .x0 = p.B := by
  obtain ⟨hS, h0, h4⟩ := h
  have hS' := hS
  obtain ⟨_, _, _, hs, -, a1, a2, hZ, hpl, -, -, -, -, -, -, -, -, -, -, d1, d2, -, -⟩ := hS'
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  unfold offQ at hZ
  exact WP.mono (wsNew_ok (o := offP p.w) (len := p.pl) hs h0 h4 (by decide) (by decide) (by decide) hpl
    (by omega) (by unfold offP; omega) (by unfold offP; omega))
    fun t ⟨hWs, hl, hw, ha, h0', f, k⟩ => ⟨⟨hS.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsP, sFn, offP] <;> omega) k, hWs, hl, hw, ha⟩, h0'⟩

/-- `q`'s workspace's base: `p`'s, in `x5`. -/
def SS2 (p : SetupPub) (t : State) : Prop :=
  SA p t ∧ t.gpr .x0 = p.B ∧ t.gpr .x5 = off p.B (offP p.w)

theorem stage2_ok {p : SetupPub} {s : State} (h : SA p s ∧ s.gpr .x0 = p.B) :
    WP isa (.block [ldh .x5 sWsP]) s (SS2 p) := by
  obtain ⟨hA, h0⟩ := h
  have hs := hA.1.scr
  have hWsP := hA.2.1
  have := hA.1.bounds
  have hn := hs.nowrap
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  unfold offQ at this
  exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = off p.B (offP p.w) ∧ t.mem = s.mem)
    (by brun [h0, hdr_enc (show sWsP < 32 by decide), hs.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hWsP])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h5, hm⟩, k⟩ => ⟨hA.frm' hm k, (k.gpr .x0 (by decide)).trans h0, h5⟩

theorem stage3_ok {p : SetupPub} {s : State} (h : SS2 p s) : WP isa (.block wsEndT) s (SS3 p) := by
  obtain ⟨hA, h0, h5⟩ := h
  have hA' := hA
  obtain ⟨⟨_, _, _, hs, -, a1, -, hZ, -⟩, -, -, hw, ha⟩ := hA'
  have hn := hs.nowrap
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  have hwp : wsWords p.pl < 2 ^ 30 := by have := hA.1.bounds; unfold wsWords; omega
  unfold offQ at hZ
  refine WP.mono (wsEndT_ok (wx := wsWords p.pl) (hs.sub (o := offP p.w)
    (n := slot (wsWords p.pl) 8) (by unfold offP; omega) (by omega)) h5 hw hwp
    (ha _ (by decide)) (Nat.le_refl _)) fun t ⟨⟨h4, hm⟩, k⟩ => ?_
  rw [off_off] at h4
  exact ⟨hA.frm' hm k, (k.gpr .x0 (by decide)).trans h0, by
    rw [h4]; exact congrArg (off p.B) (by unfold offQ offP; omega)⟩

theorem wsQ_ok {p : SetupPub} {s : State} (h : SS3 p s) :
    WP isa (.block (wsNew sWsQ sQlen)) s (SBr (·.B) p) := by
  obtain ⟨hA, h0, h4⟩ := h
  have hA' := hA
  obtain ⟨⟨_, _, _, hs, -, a1, a2, hZ, -, hql, -, -, -, -, -, -, -, -, -, d1, d2, d3, d4⟩, hWsP, hF⟩ := hA'
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega
  have hn := hs.nowrap
  unfold offQ at hZ
  refine WP.mono (wsNew_ok (o := offQ p.w p.pl) (len := p.ql) hs h0 h4 (by decide) (by decide) (by decide) hql
    (by omega) (by unfold offQ; omega) (by unfold offQ; omega))
    fun t ⟨hWs, hl, hw, ha, h0', f, k⟩ => ⟨⟨⟨hA.1.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsQ, sFn, offQ] <;> omega) k, ?_, hF.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsQ, sFn, offQ, offP] <;> omega) (by unfold offP; omega)⟩,
      hWs, hl, hw, ha⟩, h0'⟩
  rw [f.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sWsQ, sWsP, sFn, offQ] <;> omega) (by unfold sWsP sFn; omega)]
  exact hWsP

/-- Into a workspace from the modulus' (`enterP`, `enterQ`), or back (`leave`). -/
theorem SB.move {p : SetupPub} {s : State} (h : SB p s) {X : Addr} {i : Nat} {A' : Addr}
    (h0 : s.gpr .x0 = X) (hi : i < 32) (hl : InRegions (s.rd ++ s.wr) (off X (8 * i)) 8)
    (hw : word s.mem X (8 * i) = A') :
    WP isa (.block [ldh .x0 i]) s (SBr (fun _ => A') p) :=
  WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = A' ∧ t.mem = s.mem)
    (by brun [h0, hdr_enc hi, hl, hw]) rfl rfl rfl) fun t ⟨⟨h0', hm⟩, k⟩ => ⟨h.mem hm k, h0'⟩

/-- A prime's workspace context from `SB`. -/
theorem SB.sub {p : SetupPub} {s : State} (h : SB p s) {o wx : Nat} (h0 : s.gpr .x0 = off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ p.Z) :
    SubCtx s p.B p.Z o p.w wx (word s.mem (off p.B o) (8 * sMinv)) :=
  let ⟨⟨⟨_, _, _, hs, hH, _⟩, _⟩, _⟩ := h
  ⟨hs, h0, hdr_any hF.2.1 hF.2.2, hF.1, hH.hw, hH.harr, hlo, hhi⟩

/-- A load into a prime's workspace keeps `SB`. -/
theorem SB.load {p : SetupPub} {s : State} {o wx j sp sl len : Nat} {ptr : Addr} (h : SB p s)
    (hL : LPre j sp sl ⟨⟨p.B, p.Z, o, p.w, wx⟩, ptr, len⟩ s)
    (hr : offP p.w + 8 * 17 ≤ o + 256 ∧ (o + slot wx 8 ≤ offQ p.w p.pl ∨ offQ p.w p.pl + 8 * 17 ≤ o + 256)) :
    WP isa (seqs (loadArr j sp sl)) s fun t => SB p t ∧ t.gpr .x0 = off p.B o := by
  simp only [LPre] at hL
  obtain ⟨minv, bs, hc, hw2, hwx, hw30, hj, hsp, hsl, hp, hl, hbl, hsrc, hk1, hk', hkw⟩ := hL
  have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hc.scr.nowrap
  have hi : o + slot wx 8 + tabBytes wx ≤ p.Z := hc.hi
  have h8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  exact WP.mono (primeLoad_ok hc hw2 hwx hw30 hj hsp hsl hp hl hsrc hk1 hk' hkw) fun t ⟨hc', _, ho, k⟩ =>
    ⟨h.frm (Frm.of_load ho hj (by omega) (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; simp only; omega) k, hc'.x0⟩

/-- `LPre` from `SB`, in the workspace at `off B o` (`x0`). -/
theorem SB.lpre {p : SetupPub} {s : State} (h : SB p s) {o wx j sp sl len : Nat} {ptr : Addr} {bs : List Byte}
    (h0 : s.gpr .x0 = off p.B o) (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ p.Z) (hw2 : 2 ≤ wx) (hwx : wx ≤ p.w) (hj : j < 8) (hsp : sp < 32)
    (hsl : sl < 32) (hp : word s.mem p.B (8 * sp) = ptr) (hl : word s.mem p.B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hbl : bs.length = len) (hsrc : Src s p.B p.Z ptr bs) (hk1 : 1 ≤ bs.length) (hk' : bs.length < 2 ^ 31)
    (hkw : (bs.length + 7) / 8 ≤ wx) : LPre j sp sl ⟨⟨p.B, p.Z, o, p.w, wx⟩, ptr, len⟩ s :=
  ⟨_, bs, h.sub h0 hF hlo hhi, hw2, hwx, by have := h.bounds; show p.w < 2 ^ 30; omega, hj, hsp, hsl, hp, hl,
    hbl, hsrc, hk1, hk', hkw⟩

theorem lpreP {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offP p.w)) p s) :
    LPre Public.aN sP sPlen ⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.pp, p.pl⟩ s ∧
      LPre aChunk sQinv sPlen ⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.ip, p.pl⟩ s := by
  obtain ⟨hB, h0⟩ := h
  have hB' := hB
  obtain ⟨⟨⟨pb, qb, ib, hs, -, a1, a2, hZ, hpl, -, hpp, -, hip, c1, -, c3, l1, -, l3, d1, d2, -, -⟩, -, hF⟩, -⟩ := hB'
  unfold offQ at hZ
  have hw := wsWords_le d2 (by omega)
  exact ⟨hB.lpre h0 hF (Nat.le_refl _) (by unfold offP; omega) (by unfold wsWords; omega) hw (by decide)
    (by decide) (by decide) hpp (by rw [l1]; exact hpl) l1 c1 (by omega) (by omega) (by unfold wsWords; omega),
    hB.lpre h0 hF (Nat.le_refl _) (by unfold offP; omega) (by unfold wsWords; omega) hw (by decide)
    (by decide) (by decide) hip (by rw [l3]; exact hpl) l3 c3 (by omega) (by omega) (by unfold wsWords; omega)⟩

theorem lpreQ {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offQ p.w p.pl)) p s) :
    LPre Public.aN sQ sQlen ⟨⟨p.B, p.Z, offQ p.w p.pl, p.w, wsWords p.ql⟩, p.qp, p.ql⟩ s := by
  obtain ⟨hB, h0⟩ := h
  have hB' := hB
  obtain ⟨⟨⟨pb, qb, ib, hs, -, a1, a2, hZ, -, hql, -, hqp, -, -, c2, -, -, l2, -, -, -, d3, d4⟩, -, -⟩, -, hF⟩ := hB'
  exact hB.lpre h0 hF (by unfold offQ; omega) hZ (by unfold wsWords; omega) (wsWords_le d4 (by omega))
    (by decide) (by decide) (by decide) hqp (by rw [l2]; exact hql) l2 c2 (by omega) (by omega)
    (by unfold wsWords; omega)

theorem enterP_ok {p : SetupPub} {s : State} (h : SBr (·.B) p s) :
    WP isa (.block [enterP]) s (SBr (fun p => off p.B (offP p.w)) p) := by
  obtain ⟨h, h0⟩ := h
  have := h.bounds
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  exact h.move (X := p.B) (i := sWsP) h0 (by decide) (h.scr.ld (by unfold sWsP sFn offQ at *; omega)) h.1.2.1

theorem leaveP_ok {p : SetupPub} {s : State} (h : SBr (fun p => off p.B (offP p.w)) p s) :
    WP isa (.block [leave]) s (SBr (·.B) p) := by
  obtain ⟨h, h0⟩ := h
  have hF := h.1.2.2
  have := h.bounds
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  exact h.move (X := off p.B (offP p.w)) (i := sLink) h0 (by decide) ((h.scr.sub (o := offP p.w)
    (n := slot (wsWords p.pl) 8) (by unfold offQ offP at *; omega) (by omega)).ld (by unfold sLink sFn; omega)) hF.1

theorem enterQ_ok {p : SetupPub} {s : State} (h : SBr (·.B) p s) :
    WP isa (.block [enterQ]) s (SBr (fun p => off p.B (offQ p.w p.pl)) p) := by
  obtain ⟨h, h0⟩ := h
  have := h.bounds
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  exact h.move (X := p.B) (i := sWsQ) h0 (by decide) (h.scr.ld (by unfold sWsQ sFn offQ at *; omega)) h.2.1

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
    (RelCT.seq (two_piece (Ψ := SBr (·.B)) [.x0] (pins_sbr _) (by taint_decide) fun p s h => leaveP_ok h)
      (two_piece [.x0] (pins_sbr _) (by taint_decide) fun p s h => enterQ_ok h))

theorem primesSetup_eq : primesSetup = ([.block (([mov .x5 .x0] : List Instr) ++ wsEnd)] : List (Prog isa)) ++
    (([.block (wsNew sWsP sPlen)] : List (Prog isa)) ++ (([.block (([ldh .x5 sWsP] : List Instr) ++ wsEndT)] : List (Prog isa)) ++
    (([.block (wsNew sWsQ sQlen)] : List (Prog isa)) ++ (([.block [enterP]] : List (Prog isa)) ++ (loadArr Public.aN sP sPlen ++
    (loadArr aChunk sQinv sPlen ++ (([.block [leave, enterQ]] : List (Prog isa)) ++ (loadArr Public.aN sQ sQlen ++
    ([.block [leave]] : List (Prog isa)))))))))) := rfl

theorem setup_ct : SetupCT := by
  unfold SetupCT
  rw [primesSetup_eq]
  -- `p`'s workspace.
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_piece (Ψ := SS1) [.x0]
    (pins_of (fun p _ => p.B) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.sst.2) (by taint_decide)
    fun p s h => stage1_ok h) ?_)
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_piece
    (Ψ := fun p t => SA p t ∧ t.gpr .x0 = p.B) [.x0, .x4]
    (pins_ws (fun p => off p.B (offP p.w)) fun p s h => ⟨h.2.1, h.2.2⟩) (by taint_decide)
    fun p s h => wsP_ok h) ?_)
  -- `q`'s workspace.
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (RelCT.block_append
    (l₁ := ([ldh .x5 sWsP] : List Instr)) (l₂ := wsEndT) (RelCT.seq (two_piece (Ψ := SS2) [.x0]
    (pins_of (fun p _ => p.B) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2) (by taint_decide)
    fun p s h => stage2_ok h) (two_piece (Ψ := SS3) [.x5]
    (pins_of (fun p _ => off p.B (offP p.w)) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2) (by taint_decide)
    fun p s h => stage3_ok h))) ?_)
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_piece (Ψ := SBr (·.B)) [.x0, .x4]
    (pins_ws (fun p => off p.B (offQ p.w p.pl)) fun p s h => ⟨h.2.1, h.2.2⟩) (by taint_decide)
    fun p s h => wsQ_ok h) ?_)
  -- Into `p`'s workspace: `p` and `qInv`.
  refine RelCT.seqs_append (by simp) (by simp [loadArr]) (RelCT.seq (two_piece
    (Ψ := SBr fun p => off p.B (offP p.w)) [.x0] (pins_sbr _) (by taint_decide) fun p s h => enterP_ok h) ?_)
  refine RelCT.seqs_append (by simp [loadArr]) (by simp [loadArr]) (RelCT.seq (two_post
    (Ψ := SBr fun p => off p.B (offP p.w)) (two_map
    (fun p : SetupPub => (⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.pp, p.pl⟩ : BPub)) (fun p s h => (lpreP h).1)
    loadArr_ct_pN) fun p s h => loadP1_ok h) ?_)
  refine RelCT.seqs_append (by simp [loadArr]) (by simp) (RelCT.seq (two_post
    (Ψ := SBr fun p => off p.B (offP p.w)) (two_map
    (fun p : SetupPub => (⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.ip, p.pl⟩ : BPub)) (fun p s h => (lpreP h).2)
    loadArr_ct_pI) fun p s h => loadP2_ok h) ?_)
  -- Into `q`'s workspace: `q`.
  refine RelCT.seqs_append (by simp) (by simp [loadArr]) (RelCT.seq leaveEnterQ_ct ?_)
  refine RelCT.seqs_append (by simp [loadArr]) (by simp) (RelCT.seq (two_post
    (Ψ := SBr fun p => off p.B (offQ p.w p.pl)) (two_map
    (fun p : SetupPub => (⟨⟨p.B, p.Z, offQ p.w p.pl, p.w, wsWords p.ql⟩, p.qp, p.ql⟩ : BPub))
    (fun p s h => lpreQ h) loadArr_ct_qN)
    fun p s h => loadQ_ok h) ?_)
  exact two_taint [.x0] (pins_sbr _) (by taint_decide)

end VG.Proof.Bignum.AArch64
