module

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRoundAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRoundAll
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.CrtExp
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMr
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWin
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrTab
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMr
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWin
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrTab
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW

/-! ### `RsaKeyGen.X86_64.CTMrExp`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.CTMrWin`, which only this module used -/

section

/-!
# A candidate on x86-64: constant time of a window of Miller–Rabin

`mrWin` in pieces: each squaring's multiplication and its comparison, the
digit with the selection of its entry, the multiplication by it, and the
comparisons and the flag. Between them, what each run keeps (`WinW`): the
header, and enough of the arithmetic for the multiplications to run
(`MrCtx`, the table, `y < c`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The public data of a window: Miller–Rabin's, the witnesses so far, the
octets read, the words left and the windows left of the word. -/
structure WPub where
  p : MrPub
  i : Nat
  u : Nat
  k : Nat
  n : Nat

/-- The header words public during a window. -/
abbrev WPub.vs (q : WPub) : List (Nat × BitVec 64) :=
  q.p.vs q.i q.u ++ [(kWords, BitVec.ofNat 64 (q.k - 1)), (kBits, BitVec.ofNat 64 q.n)]

theorem MrPub.vs_lt (p : MrPub) (i u : Nat) (ex : List (Nat × BitVec 64)) (hex : ∀ e ∈ ex, e.1 < 32) :
    ∀ e ∈ p.vs i u ++ ex, e.1 < 32 := fun e he => by
  rcases List.mem_append.mp he with he | he
  · have h1 : e.1 ∈ mrS := by
      have := List.mem_map_of_mem (f := (·.1)) he
      rwa [show (p.vs i u).map (·.1) = mrS by simp only [MrPub.vs, mrS, List.map_cons, List.map_nil]] at this
    have h2 : ∀ j ∈ mrS, j < 32 := by decide
    exact h2 _ h1
  · exact hex e he

theorem WPub.vs_lt (q : WPub) : ∀ e ∈ q.vs, e.1 < 32 :=
  q.p.vs_lt q.i q.u _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; decide)

theorem WPub.vs_fst (q : WPub) : q.vs.map (·.1) = mrS ++ [kWords, kBits] := q.p.vs_fst q.i q.u _

/-- `HP` of a window's header after changes away from its words. -/
theorem WPub.hp_frm {q : WPub} {s t : State} {rs : List (Nat × Nat)} (h : HP q.p.B q.p.wr q.vs s)
    (hf : Frm q.p.B rs s.mem t.mem)
    (hd : ∀ j ∈ mrS ++ [kWords, kBits], j < 32 ∧ ∀ r ∈ rs, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j)
    (hdi : t.gpr .rdi = q.p.B) (hw : t.wr = s.wr) : HP q.p.B q.p.wr q.vs t :=
  ⟨hdi, hw.trans h.wr, hdr_frm hf (fun e he => hd e.1 (by rw [← q.vs_fst]; exact List.mem_map_of_mem he)) h.hdr⟩

/-- What each run keeps between the pieces of a window. -/
def WinW (q : WPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr q.vs s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (c b bm : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧ TabOK s.mem q.p.B q.p.w c b ∧
      c % 2 = 1 ∧ 1 < c ∧ wv s.mem q.p.B (slot q.p.w aY) q.p.w < c

theorem WinW.goodW {q : WPub} {s : State} (h : WinW q s) : GoodW ⟨q.p.B, q.p.Z, q.p.w⟩ s :=
  let ⟨_, _, hd, mi, _, _, _, hc, _⟩ := h; ⟨mi, hc.good, hd.z⟩

/-- `WinW` after a multiplication `y := y b`. -/
theorem winW_mm (M : Mont) {q : WPub} {s : State} (h : WinW q s) {b : Nat} (hb : b < 8)
    (d4 : b ≠ aAcc) (d6 : b ≠ aTmp)
    (hB : wv s.mem q.p.B (slot q.p.w b) q.p.w < wv s.mem q.p.B (slot q.p.w aN) q.p.w) :
    WP isa (M.mm aY aY b) s fun t => WinW q t := by
  obtain ⟨hk, hp, hd, mi, c, b', bm, hc, hT, hodd, hc1, hy⟩ := h
  have hw' : q.p.w < 2 ^ 31 := by have := hd.w128; omega_arith
  refine WP.mono (M.mm_ok hc.good hd.z (by have := hd.w4; omega_arith) hw' (o := aY) (a := aY) (b := b) (by decide)
    (by decide) hb (by decide) (by decide) (by decide) d4 hc.inv hB (by decide) d6) fun t ⟨hg, hlt, _, ha', k⟩ => ?_
  have hf : Frm q.p.B [(slot q.p.w aAcc, 8 * (q.p.w + 2)), (slot q.p.w aTmp, 8 * (q.p.w + 2)),
      (slot q.p.w aY, 8 * (q.p.w + 2))] s.mem t.mem := Frm.of_arrays ha' (by simp)
  refine ⟨hk, hp.frm hf ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) q.vs_lt hg.rdi k.2.2, hd, mi, c, b', bm,
    hc.of_frm hd hf hg.scr hg.rdi ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl),
    hT.of_low hf ((VG.Proof.RsaKeyGen.mm_shape _ _).leD rfl rfl) (by have := hd.w128; omega_arith), hodd, hc1, by rw [← hc.n]; exact hlt⟩

/-- The comparison and the flag after a squaring keep `WinW`. -/
theorem winW_sqTail {q : WPub} {s : State} (h : WinW q s) :
    WP isa (seqs (eqMask aRm1 ++ ([.block [.mov .rax (.mem (hdr kFlag)), .alu .or .rax (.reg .rbp),
      .store (hdr kFlag) .rax]] : List (Prog isa)))) s fun t => WinW q t := by
  obtain ⟨hk, hp, hd, mi, c, b, bm, hc, hT, hodd, hc1, hy⟩ := h
  have hg := hc.good
  have hn := hg.scr.nowrap
  have hw' : q.p.w < 2 ^ 31 := by have := hd.w128; omega_arith
  refine wp_seqs_append (by simp [eqMask]) (by simp) (WP.mono (eqMask_ok hg hd.z (by have := hd.w4; omega_arith) hw'
    (j := aRm1) (by decide) hd.x) fun s₁ ⟨_, hm₁, k₁⟩ => ?_)
  have hdi₁ : s₁.gpr .rdi = q.p.B := (k₁.gpr (by decide)).trans hg.rdi
  have hs₁ := hg.scr.congr k₁.2.2
  have hl : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off q.p.B (8 * i)) 8 := fun i hi =>
    hs₁.ld (by have := hdr_lt_slot q.p.w 8 hi; have := hd.z; omega_arith)
  have hst : InRegions s₁.wr (off q.p.B (8 * kFlag)) 8 :=
    hs₁.st (by have := hdr_lt_slot q.p.w 8 (show kFlag < 32 by decide); have := hd.z; omega_arith)
  simp only [seqs]
  refine WP.mono (WP.keep [.rax] (Q := fun t => ∃ v : BitVec 64, t.mem = s₁.mem.writeW (off q.p.B (8 * kFlag)) v) (by
    xrun [State.ea, hdr, hdi₁, hdrOff, hl kFlag (by decide), hst]
    exact ⟨_, rfl⟩) rfl) fun t ⟨⟨v, hm⟩, k⟩ => ?_
  have hf : Frm q.p.B [(8 * kFlag, 8)] s.mem t.mem := by
    rw [hm, hm₁]; exact Frm.of_outside (writeW_outside _ _ _ (by unfold kFlag kPlen sFn; omega_arith)) (by simp)
  have hgt : Good t q.p.B q.p.Z q.p.w mi := ⟨hs₁.congr k.2.2, (k.gpr (by decide)).trans hdi₁,
    Hdr.of_frm hg.hdr hf ((VG.Proof.RsaKeyGen.hdr_shape 0 _).geD rfl rfl)⟩
  refine ⟨hk, WPub.hp_frm hp hf (by decide) hgt.rdi
    (k.2.2.trans k₁.2.2), hd, mi, c, b, bm,
    hc.of_frm hd hf hgt.scr hgt.rdi ((VG.Proof.RsaKeyGen.hdr_shape 0 _).geD rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl),
    hT.of_low hf ((VG.Proof.RsaKeyGen.hdr_shape _ _).leD rfl rfl) hw', hodd, hc1, ?_⟩
  rw [hf.wv_eq (d := slot q.p.w aY) (k := q.p.w) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl)
    (by have := slot_le (w := q.p.w) (show aY < 8 by decide); have := hd.z; omega_arith)]
  exact hy

/-- A squaring leaks the same in runs that agree on the public data. -/
theorem mrSq_ct (M : Mont) : RelCT isa (Two WinW) (seqs (mrSq M.mm)) (Two WinW) := by
  rw [mrSq_eq]
  refine RelCT.seqs_app (by simp) (by simp [eqMask]) (RelCT.seq (R := Two WinW) ?_ ?_)
  · simp only [seqs]
    refine two_post (two_map (fun q : WPub => (⟨q.p.B, q.p.Z, q.p.w⟩ : Ws)) (fun _ _ h => h.goodW)
      (M.ct (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) fun q s h => winW_mm M h (by decide) (by decide) (by decide) ?_
    obtain ⟨_, _, hd, mi, c, b, bm, hc, -, -, -, hy⟩ := h
    rw [hc.n]; exact hy
  · exact kt_piece (fun q : WPub => q.p.B) (fun q => q.p.wr) (mrS ++ [kWords, kBits]) WPub.vs [] (by decide)
      WPub.vs_fst (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) fun _ _ h => winW_sqTail h

/-- The public header words apart from `kG` and an array. -/
theorem mrS_kG_slot (w a : Nat) : ∀ j ∈ mrS ++ [kWords, kBits], j < 32 ∧
    ∀ r ∈ [(8 * kG, 8), (slot w a, 8 * (w + 2))], 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  have h : ∀ j ∈ mrS ++ [kWords, kBits], j < 32 ∧ 8 * j + 8 ≤ VG.Impl.Bignum.hdrBytes ∧
      (8 * j + 8 ≤ 8 * kG ∨ 8 * kG + 8 ≤ 8 * j) := by
    decide
  intro j hj
  refine ⟨(h j hj).1, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨(h j hj).2.2, .inl (Nat.le_trans (h j hj).2.1 (Nat.le_add_right _ _))⟩

/-- What the digit and its entry change: `kG` and `aXm`. -/
theorem kgXm_shape (w : Nat) :
    VG.Proof.RsaKeyGen.SlotShape w [(8 * kG, 8), (slot w aXm, 8 * (w + 2))] [(8 * kG, 8)] [aXm] := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [.inl (.head _), .inr ⟨_, .head _, rfl⟩]

/-- The digit and its entry keep `WinW`, with the entry below `c`. -/
theorem winW_sel {q : WPub} {s : State} (h : WinW q s) :
    WP isa (seqs (([.block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 60, .store (hdr kG) .rax]] : List (Prog isa)) ++ mrSel)) s fun t =>
      WinW q t ∧ wv t.mem q.p.B (slot q.p.w aXm) q.p.w < wv t.mem q.p.B (slot q.p.w aN) q.p.w := by
  obtain ⟨hk, hp, hd, mi, c, b, bm, hc, hT, hodd, hc1, hy⟩ := h
  have hg := hc.good
  have hn := hg.scr.nowrap
  have hw' : q.p.w < 2 ^ 30 := by have := hd.w128; omega_arith
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off q.p.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot q.p.w 8 hi; have := hd.z; omega_arith)
  have hst : InRegions s.wr (off q.p.B (8 * kG)) 8 :=
    hg.scr.st (by have := hdr_lt_slot q.p.w 8 (show kG < 32 by decide); have := hd.z; omega_arith)
  have hTZ : slot q.p.w 8 + tabBytes q.p.w ≤ q.p.Z := by rw [tab_end]; have := aE_fits hd; omega_arith
  refine wp_seqs_append (by simp) (by simp [mrSel]) ?_
  simp only [seqs]
  generalize hd' : (word s.mem q.p.B (8 * kV) >>> 60).toNat = d
  have hd16 : d < 16 := hd' ▸ top_nibble _
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off q.p.B (8 * kG)) (BitVec.ofNat 64 d)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl kV (by decide), hst]
    rw [← hd', BitVec.ofNat_toNat, BitVec.setWidth_eq]) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hf₁ : Frm q.p.B [(8 * kG, 8)] s.mem s₁.mem := by
    rw [hm₁]; exact Frm.of_outside (writeW_outside _ _ _ (by unfold kG sFn; omega_arith)) (by simp)
  have hg₁ : Good s₁ q.p.B q.p.Z q.p.w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi,
    Hdr.of_frm hg.hdr hf₁ ((VG.Proof.RsaKeyGen.hdr_shape 0 _).geD rfl rfl)⟩
  refine WP.mono (mrSel_ok hg₁ hTZ (by have := hd.w4; omega_arith) hw' hd16 (by rw [hm₁, word_writeW_self]))
    fun t ⟨hv, ho, k⟩ => ?_
  have hf : Frm q.p.B [(8 * kG, 8), (slot q.p.w aXm, 8 * (q.p.w + 2))] s.mem t.mem :=
    (hf₁.mono (by simp)).trans (Frm.of_outside ho (by simp))
  have hgt : Good t q.p.B q.p.Z q.p.w mi := ⟨hg₁.scr.congr k.2.2, (k.gpr (by decide)).trans hg₁.rdi,
    Hdr.of_frm hg.hdr hf ((kgXm_shape _).geD rfl rfl)⟩
  have hct := hc.of_frm hd hf hgt.scr hgt.rdi ((kgXm_shape _).geD rfl rfl) ((kgXm_shape _).apartW rfl rfl) ((kgXm_shape _).apartW rfl rfl) ((kgXm_shape _).apartW rfl rfl) ((kgXm_shape _).apartW rfl rfl)
  refine ⟨⟨hk, WPub.hp_frm hp hf (mrS_kG_slot _ _) hgt.rdi
    (k.2.2.trans k₁.2.2), hd, mi, c, b, bm, hct, hT.of_low hf ((kgXm_shape _).leD rfl rfl) (by omega_arith), hodd, hc1, ?_⟩, ?_⟩
  · rw [hf.wv_eq (d := slot q.p.w aY) (k := q.p.w) ((kgXm_shape _).apartW rfl rfl)
      (by have := slot_le (w := q.p.w) (show aY < 8 by decide); have := hd.z; omega_arith)]
    exact hy
  · rw [hv, hct.n, hf₁.wv_eq (d := slot q.p.w (8 + d)) (k := q.p.w)
      (fun r hr => by simp at hr; subst hr; right; have := hdr_lt_slot q.p.w (8 + d) (show kG < 32 by decide); omega_arith)
      (by have := slot_lt24 q.p.w (show 8 + d + 1 ≤ 24 by omega_arith); have := slot_succ q.p.w (8 + d); omega_arith),
      hT d hd16]
    exact Nat.mod_lt _ (by omega_arith)

/-- The digit of a window into `kG`. -/
def winDigit : List (Prog isa) := [.block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 60, .store (hdr kG) .rax]]

/-- The end of a window: the comparisons, the flag, `kV` and `kBits`. -/
def winTail : List (Prog isa) :=
  eqMask aRm1 ++ [.block [.store (hdr kG) .rbp]] ++ eqMask aR1 ++
  [.block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 60, .alu .cmp .rax (.imm 1),
    .alu .sbb .r15 (.reg .r15), .mov .rdx (.mem (hdr kG)), .alu .or .rbp (.reg .rdx),
    .mov .rax (.mem (hdr kFlag)), .alu .and .rax (.reg .r15), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))),
    .alu .and .rbp (.reg .r15), .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax,
    .mov .rax (.mem (hdr kV)), .shift .shl .rax 4, .store (hdr kV) .rax,
    .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]

theorem mrWin_eq' (mul : Nat → Nat → Nat → Prog isa) : mrWin mul =
    mrSq mul ++ (mrSq mul ++ (mrSq mul ++ (mrSq mul ++ ((winDigit ++ mrSel) ++ ([mul aY aY aXm] ++ winTail))))) := by
  simp only [mrWin, winDigit, winTail, List.append_assoc]

/-- A window leaks the same in runs that agree on the public data. -/
theorem mrWin_ct (M : Mont) : RelCT isa (Two WinW) (seqs (mrWin M.mm)) fun _ _ => True := by
  rw [mrWin_eq']
  refine RelCT.seqs_app (by simp [mrSq]) (by simp [mrSq]) (RelCT.seq (mrSq_ct M) ?_)
  refine RelCT.seqs_app (by simp [mrSq]) (by simp [mrSq]) (RelCT.seq (mrSq_ct M) ?_)
  refine RelCT.seqs_app (by simp [mrSq]) (by simp [mrSq]) (RelCT.seq (mrSq_ct M) ?_)
  refine RelCT.seqs_app (by simp [mrSq]) (by simp [mrSel]) (RelCT.seq (mrSq_ct M) ?_)
  refine RelCT.seqs_app (by simp [mrSel, winDigit]) (by simp) (RelCT.seq (R := Two fun q s => WinW q s ∧
    wv s.mem q.p.B (slot q.p.w aXm) q.p.w < wv s.mem q.p.B (slot q.p.w aN) q.p.w) ?_ ?_)
  · exact kt_piece (fun q : WPub => q.p.B) (fun q => q.p.wr) (mrS ++ [kWords, kBits]) WPub.vs [] (by decide)
      WPub.vs_fst (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) fun _ _ h => winW_sel h
  refine RelCT.seqs_app (by simp) (by simp [winTail, eqMask]) (RelCT.seq (R := Two WinW) ?_ ?_)
  · simp only [seqs]
    exact two_post (two_map (fun q : WPub => (⟨q.p.B, q.p.Z, q.p.w⟩ : Ws)) (fun _ _ h => h.1.goodW)
      (M.ct (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))) fun q s h => winW_mm M h.1 (by decide) (by decide)
        (by decide) h.2
  · exact kt_ct (fun q : WPub => q.p.B) (fun q => q.p.wr) (mrS ++ [kWords, kBits]) WPub.vs [] (by decide)
      WPub.vs_fst (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide)

end VG.Proof.RsaKeyGen.X86_64

end

end

/-!
# A candidate on x86-64: constant time of Miller–Rabin's exponentiation

Its loops over the words of `E` and their windows, with the invariants of
their correctness proofs (`WordInv`, `WinInv`) from the state `s₀` where
the exponentiation starts, whose header holds the public words (`EBase`);
then the three squarings after them.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The public data of the exponentiation. -/
structure EPub where
  p : MrPub
  i : Nat
  u : Nat

/-- Where the exponentiation starts. -/
def EBase (q : EPub) (s₀ : State) : Prop :=
  KW q.p.B q.p.wr ∧ (∀ e ∈ q.p.vs q.i q.u, word s₀.mem q.p.B (8 * e.1) = e.2) ∧ s₀.wr = q.p.wr ∧
    MrDims q.p.B q.p.Z q.p.w

theorem mrS_exp (w : Nat) : ∀ j ∈ mrS, ∀ r ∈ expRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  have h : ∀ j ∈ mrS, 8 * j + 8 ≤ VG.Impl.Bignum.hdrBytes ∧ ∀ h ∈ ([(248, 8), (176, 8), (208, 8), (224, 8),
      (216, 8)] : List (Nat × Nat)), 8 * j + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * j := by
    decide
  exact fun j hj => VG.Proof.RsaKeyGen.hdr_of_shape (expRanges_shape w) (h j hj).1 (h j hj).2

theorem vs_exp' (p : MrPub) (i u : Nat) :
    ∀ e ∈ p.vs i u, e.1 < 32 ∧ ∀ r ∈ [(8 * kFlag, 8)], 8 * e.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * e.1 := fun e he => by
  have h1 : e.1 ∈ mrS := by
    have := List.mem_map_of_mem (f := (·.1)) he
    rwa [show (p.vs i u).map (·.1) = mrS by simp only [MrPub.vs, mrS, List.map_cons, List.map_nil]] at this
  have h2 : ∀ j ∈ mrS, j < 32 ∧ ∀ r ∈ [(8 * kFlag, 8)], 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
    decide
  exact h2 _ h1

theorem vs_exp (p : MrPub) (i u : Nat) :
    ∀ e ∈ p.vs i u, e.1 < 32 ∧ ∀ r ∈ expRanges p.w, 8 * e.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * e.1 := fun e he => by
  have h1 : e.1 ∈ mrS := by
    have := List.mem_map_of_mem (f := (·.1)) he
    rwa [show (p.vs i u).map (·.1) = mrS by simp only [MrPub.vs, mrS, List.map_cons, List.map_nil]] at this
  have h2 : ∀ j ∈ mrS, j < 32 := by decide
  exact ⟨h2 _ h1, mrS_exp p.w _ h1⟩

/-- After `j` windows of word `k − 1`. -/
def WinL (a : EPub × Nat) (j : Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (c bm b : Nat) (W : BitVec 64) (s₀ : State), EBase a.1 s₀ ∧
    WinInv a.1.p.B a.1.p.Z a.1.p.w mi c bm b a.2 W s₀ j s ∧ c % 2 = 1 ∧ 1 < c ∧ 1 ≤ a.2 ∧
    a.2 ≤ a.1.p.w ∧ W.toNat = Proof.RsaKeyGen.mrE c / 2 ^ (64 * (a.2 - 1)) % 2 ^ 64

/-- The header in a word. -/
theorem winL_hp {a : EPub × Nat} {j : Nat} {s : State} (h : WinL a j s) :
    HP a.1.p.B a.1.p.wr (a.1.p.vs a.1.i a.1.u ++
      [(kWords, BitVec.ofNat 64 (a.2 - 1)), (kBits, BitVec.ofNat 64 (16 - j))]) s := by
  obtain ⟨mi, c, bm, b, W, s₀, ⟨_, hh, hw, _⟩, hI, -⟩ := h
  refine ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hdr_frm hI.frm (vs_exp _ _ _) hh e he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hI.words
    · exact hI.bits

theorem winL_winW {a : EPub × Nat} {j : Nat} {s : State} (h : WinL a j s) :
    WinW ⟨a.1.p, a.1.i, a.1.u, a.2, 16 - j⟩ s := by
  have hp := winL_hp h
  obtain ⟨mi, c, bm, b, W, s₀, ⟨hk, _, _, hd⟩, hI, hodd, hc1, -⟩ := h
  exact ⟨hk, hp, hd, mi, c, b, bm, hI.ctx, hI.tab, hodd, hc1, by rw [hI.y]; exact Nat.mod_lt _ (by omega_using [hodd])⟩

/-- The windows of a word leak the same in runs that agree on the public data. -/
theorem wins_ct (M : Mont) :
    RelCT isa (Two fun (a : EPub × Nat) s => 0 < 16 ∧ WinL a 0 s) (.loop (seqs (mrWin M.mm)) .ne)
      (Two fun a s => WinL a 16 s) := by
  refine two_loop (Φ := WinL) (fun _ => 16)
    (two_map (fun p => (⟨p.1.1.p, p.1.1.i, p.1.1.u, p.1.2, 16 - p.2⟩ : WPub)) (fun _ _ h => winL_winW h.2)
      (mrWin_ct M)) ?_
  rintro a j s hj ⟨mi, c, bm, b, W, s₀, hE, hI, hodd, hc1, hk, hkw, hWc⟩
  refine WP.mono (mrWinStep_ok M hE.2.2.2 hodd hc1 hk hkw hWc hj hI) fun t ⟨hz, hI'⟩ => ⟨?_, fun _ => ?_, fun _ => ?_⟩
  · simp only [eval, hz, Option.map_some, Option.some.injEq]
    by_cases h : j + 1 = 16 <;> simp [h]; omega_using [hj, h]
  · exact ⟨mi, c, bm, b, W, s₀, hE, hI', hodd, hc1, hk, hkw, hWc⟩
  · rename_i e; rw [← e]; exact ⟨mi, c, bm, b, W, s₀, hE, hI', hodd, hc1, hk, hkw, hWc⟩

/-- After `j` of the `w` words. -/
def WordL (q : EPub) (j : Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (c bm b : Nat) (s₀ : State), EBase q s₀ ∧ ECtx s₀.mem q.p.B q.p.w c ∧
    WordInv q.p.B q.p.Z q.p.w mi c bm b s₀ j s ∧ c % 2 = 1 ∧ 1 < c

theorem wordL_hp {q : EPub} {j : Nat} {s : State} (h : WordL q j s) :
    HP q.p.B q.p.wr (q.p.vs q.i q.u ++ [(kWords, BitVec.ofNat 64 (q.p.w - j))]) s := by
  obtain ⟨mi, c, bm, b, s₀, ⟨_, hh, hw, _⟩, _, hI, -⟩ := h
  refine ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hdr_frm hI.frm (vs_exp _ _ _) hh e he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; exact hI.words

theorem vs_fst1 (p : MrPub) (i u : Nat) (x : BitVec 64) : (p.vs i u ++ [(kWords, x)]).map (·.1) = mrS ++ [kWords] :=
  p.vs_fst i u _

theorem vs_fst2 (p : MrPub) (i u : Nat) (x y : BitVec 64) :
    (p.vs i u ++ [(kWords, x), (kBits, y)]).map (·.1) = mrS ++ [kWords, kBits] := p.vs_fst i u _

theorem vs_fst0 (p : MrPub) (i u : Nat) : (p.vs i u).map (·.1) = mrS := by
  simpa using p.vs_fst i u []

/-- The words of the exponentiation leak the same in runs that agree on the
public data. -/
theorem words_ct (M : Mont) :
    RelCT isa (Two fun (q : EPub) s => 0 < q.p.w ∧ WordL q 0 s)
      (.loop (seqs [
        .block (([.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax] : List Instr) ++
          extBase aE .rdx ++ ([.mov .rax (.mem (hdr kWords)), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
          .mov32 .rcx (.imm 16), .store (hdr kBits) .rcx] : List Instr)),
        .loop (seqs (mrWin M.mm)) .ne,
        .block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]]) .ne)
      (Two fun q s => WordL q q.p.w s) := by
  refine two_loop (Φ := WordL) (fun q => q.p.w) ?_ ?_
  · simp only [seqs]
    refine RelCT.seq (R := Two fun (p : EPub × Nat) s => 0 < 16 ∧ WinL (p.1, p.1.p.w - p.2) 0 s)
      (kt_piece (fun p : EPub × Nat => p.1.p.B) (fun p => p.1.p.wr) (mrS ++ [kWords])
        (fun p => p.1.p.vs p.1.i p.1.u ++ [(kWords, BitVec.ofNat 64 (p.1.p.w - p.2))]) [] (by decide)
        (fun p => vs_fst1 _ _ _ _)
        (fun _ _ h => ⟨let ⟨_, _, _, _, _, hE, _⟩ := h.2; hE.1, wordL_hp h.2⟩) (pins_nil _) (by taint_decide) ?_)
      (RelCT.seq ((wins_ct M).mono (fun _ _ h => two_bind (fun p _ _ h₁ h₂ => ⟨(p.1, p.1.p.w - p.2), h₁, h₂⟩) h)
        fun _ _ h => h) ?_)
    · rintro ⟨q, j⟩ s ⟨hj, mi, c, bm, b, s₀, hE, hx, hI, hodd, hc1⟩
      dsimp only at hj
      have hd := hE.2.2.2
      have hn := hI.ctx.good.scr.nowrap
      have hxs : ECtx s.mem q.p.B q.p.w c := hx.of_low hI.frm (expRanges_low _) (by
        have := aE_fits hd; have := hd.z; omega_arith)
      have hj' : j < q.p.w := hj
      refine WP.mono (wordStart_ok hd hj' hI) fun t hB => ⟨by decide, mi, c, bm, b, _, s₀, hE, hB, hodd, hc1,
        (show 1 ≤ q.p.w - j by omega_using [hj]), (show q.p.w - j ≤ q.p.w by omega_using []), ?_⟩
      rw [← hxs.e]; exact word_of_wv s.mem q.p.B (slot q.p.w aE) q.p.w (show q.p.w - j - 1 < q.p.w by omega_using [hj])
    · exact kt_ct (fun a : EPub × Nat => a.1.p.B) (fun a => a.1.p.wr) (mrS ++ [kWords, kBits])
        (fun a => a.1.p.vs a.1.i a.1.u ++
          [(kWords, BitVec.ofNat 64 (a.2 - 1)), (kBits, BitVec.ofNat 64 (16 - 16))]) [] (by decide)
        (fun a => vs_fst2 _ _ _ _ _) (fun _ _ h => ⟨let ⟨_, _, _, _, _, _, hE, _⟩ := h; hE.1, winL_hp h⟩)
        (pins_nil _) (by taint_decide)
  · rintro q j s hj ⟨mi, c, bm, b, s₀, hE, hx, hI, hodd, hc1⟩
    have hd := hE.2.2.2
    have hn := hI.ctx.good.scr.nowrap
    refine WP.mono (mrWord_ok M hd (hx.of_low hI.frm (expRanges_low _) (by
      have := aE_fits hd; have := hd.z; omega_arith)) hodd hc1 hj hI) fun t ⟨hz, hI'⟩ => ⟨?_, fun _ => ?_, fun _ => ?_⟩
    · simp only [eval, hz, Option.map_some, Option.some.injEq]
      by_cases h : j + 1 = q.p.w <;> simp [h]; omega_using [hj, h]
    · exact ⟨mi, c, bm, b, s₀, hE, hx, hI', hodd, hc1⟩
    · rename_i e; rw [← e]; exact ⟨mi, c, bm, b, s₀, hE, hx, hI', hodd, hc1⟩

/-- What the exponentiation needs. -/
def ExpPre (q : EPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i q.u) s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (c bm b : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧ TabOK s.mem q.p.B q.p.w c b ∧
      ECtx s.mem q.p.B q.p.w c ∧ c % 2 = 1 ∧ 1 < c ∧ wv s.mem q.p.B (slot q.p.w aY) q.p.w = 2 ^ (64 * q.p.w) % c

/-- What each run keeps between the squarings after the windows. -/
def LastW (q : EPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i q.u) s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (c bm : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧ ECtx s.mem q.p.B q.p.w c ∧
      c % 2 = 1 ∧ 1 < c ∧ wv s.mem q.p.B (slot q.p.w aY) q.p.w < c

theorem LastW.goodW {q : EPub} {s : State} (h : LastW q s) : GoodW ⟨q.p.B, q.p.Z, q.p.w⟩ s :=
  let ⟨_, _, hd, mi, _, _, hc, _⟩ := h; ⟨mi, hc.good, hd.z⟩

/-- `LastW` after `y := y²`. -/
theorem lastW_mm (M : Mont) {q : EPub} {s : State} (h : LastW q s) : WP isa (M.mm aY aY aY) s fun t => LastW q t := by
  obtain ⟨hk, hp, hd, mi, c, bm, hc, hE, hodd, hc1, hy⟩ := h
  have hw' : q.p.w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hn := hc.good.scr.nowrap
  refine WP.mono (M.mm_ok hc.good hd.z (by have := hd.w4; omega_arith) hw' (o := aY) (a := aY) (b := aY) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv (by rw [hc.n]; exact hy))
    fun t ⟨hg, hlt, _, ha', k⟩ => ?_
  have hf : Frm q.p.B [(slot q.p.w aAcc, 8 * (q.p.w + 2)), (slot q.p.w aTmp, 8 * (q.p.w + 2)),
      (slot q.p.w aY, 8 * (q.p.w + 2))] s.mem t.mem := Frm.of_arrays ha' (by simp)
  refine ⟨hk, hp.frm hf ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) (q.p.vs_lt _ _ [] (by simp) |> fun h e he => h e (by simpa using he)) hg.rdi k.2.2,
    hd, mi, c, bm, hc.of_frm hd hf hg.scr hg.rdi ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl),
    hE.of_low hf ((VG.Proof.RsaKeyGen.mm_shape _ _).leD rfl rfl) (by have := aE_fits hd; have := hd.z; omega_arith), hodd, hc1, by rw [← hc.n]; exact hlt⟩

theorem mrLast_eq' (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : mrLast mul j = ([mul aY aY aY] : List (Prog isa)) ++ (eqMask aRm1 ++
    ([.block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .movImm64 .rdx (sigK j),
    .alu .and .rdx (.mem (ix .rbx .r12)), .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rbp (.reg .rdx), .mov .rax (.mem (hdr kFlag)),
    .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax] : List Instr))] : List (Prog isa))) := by
  simp only [mrLast, List.append_assoc]

/-- The comparison and the flag after a squaring keep `LastW`. -/
theorem lastW_tail {q : EPub} {s : State} (h : LastW q s) (j : Nat) :
    WP isa (seqs (eqMask aRm1 ++ ([.block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .movImm64 .rdx (sigK j),
      .alu .and .rdx (.mem (ix .rbx .r12)), .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx),
      .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rbp (.reg .rdx), .mov .rax (.mem (hdr kFlag)),
      .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax] : List Instr))] : List (Prog isa)))) s fun t => LastW q t := by
  obtain ⟨hk, hp, hd, mi, c, bm, hc, hE, hodd, hc1, hy⟩ := h
  have hg := hc.good
  have hn := hg.scr.nowrap
  have hw' : q.p.w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hEZ := aE_fits hd
  refine wp_seqs_append (by simp [eqMask]) (by simp) (WP.mono (eqMask_ok hg hd.z (by have := hd.w4; omega_arith) hw'
    (j := aRm1) (by decide) hd.x) fun s₁ ⟨_, hm₁, k₁⟩ => ?_)
  have hg₁ : Good s₁ q.p.B q.p.Z q.p.w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  simp only [seqs]
  rw [WP.block_append_iff]
  refine WP.mono (extBase_ok hg₁ hd.z hw' (j := aE) (by decide) (r := .rbx) (by decide) rfl rfl)
    fun s₂ ⟨hbx, hm₂, k₂⟩ => ?_
  have hs₂ := hg₁.scr.congr k₂.2.2
  have hdi₂ : s₂.gpr .rdi = q.p.B := (k₂.gpr (by decide)).trans hg₁.rdi
  have hl : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off q.p.B (8 * i)) 8 := fun i hi =>
    hs₂.ld (by have := hdr_lt_slot q.p.w 8 hi; have := hd.z; omega_arith)
  have hst : InRegions s₂.wr (off q.p.B (8 * kFlag)) 8 :=
    hs₂.st (by have := hdr_lt_slot q.p.w 8 (show kFlag < 32 by decide); have := hd.z; omega_arith)
  refine WP.mono (WP.keep [.rax, .rdx, .rbp, .r12] (Q := fun t => ∃ v : BitVec 64,
      t.mem = s₂.mem.writeW (off q.p.B (8 * kFlag)) v) (by
    xrun [State.ea, hdr, ix, hdi₂, hdrOff, hl kFlag (by decide), hl sW (by decide), hst, hm₂, hg₁.hdr.hw, hbx,
      addr0 rfl rfl, hs₂.ld (d := slot q.p.w aE + 8 * q.p.w) (by omega_arith)]
    exact ⟨_, rfl⟩) rfl) fun t ⟨⟨v, hm⟩, k⟩ => ?_
  have hf : Frm q.p.B [(8 * kFlag, 8)] s.mem t.mem := by
    rw [hm, hm₂, hm₁]; exact Frm.of_outside (writeW_outside _ _ _ (by unfold kFlag kPlen sFn; omega_arith)) (by simp)
  have hgt : Good t q.p.B q.p.Z q.p.w mi := ⟨hs₂.congr k.2.2, (k.gpr (by decide)).trans hdi₂,
    Hdr.of_frm hg.hdr hf ((VG.Proof.RsaKeyGen.hdr_shape 0 _).geD rfl rfl)⟩
  refine ⟨hk, ⟨hgt.rdi, (k.2.2.trans (k₂.2.2.trans k₁.2.2)).trans hp.wr,
    hdr_frm hf (vs_exp' _ _ _) hp.hdr⟩, hd, mi, c, bm,
    hc.of_frm hd hf hgt.scr hgt.rdi ((VG.Proof.RsaKeyGen.hdr_shape 0 _).geD rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl),
    hE.of_frm hf ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW1 rfl rfl) (by omega_arith), hodd, hc1, ?_⟩
  rw [hf.wv_eq (d := slot q.p.w aY) (k := q.p.w) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl)
    (by have := slot_le (w := q.p.w) (show aY < 8 by decide); have := hd.z; omega_arith)]
  exact hy

/-- A squaring after the windows leaks the same in runs that agree on the
public data. -/
theorem mrLast_ct (M : Mont) {j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    RelCT isa (Two LastW) (seqs (mrLast M.mm j)) (Two LastW) := by
  rw [mrLast_eq']
  refine RelCT.seqs_app (by simp) (by simp [eqMask]) (RelCT.seq (R := Two LastW) ?_ ?_)
  · simp only [seqs]
    exact two_post (two_map (fun q : EPub => (⟨q.p.B, q.p.Z, q.p.w⟩ : Ws)) (fun _ _ h => h.goodW)
      (M.ct (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) fun q s h => lastW_mm M h
  · rcases hj with rfl | rfl | rfl
    all_goals
      exact kt_piece (fun q : EPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i q.u) [] (by decide)
        (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) fun _ _ h => lastW_tail h _

theorem wordL_lastW {q : EPub} {s : State} (h : WordL q q.p.w s) : LastW q s := by
  obtain ⟨mi, c, bm, b, s₀, ⟨hk, hh, hw, hd⟩, hx, hI, hodd, hc1⟩ := h
  have hn := hI.ctx.good.scr.nowrap
  exact ⟨hk, ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => hdr_frm hI.frm (vs_exp _ _ _) hh e he⟩, hd, mi, c,
    bm, hI.ctx, hx.of_low hI.frm (expRanges_low _) (by have := aE_fits hd; have := hd.z; omega_arith), hodd, hc1,
    by rw [hI.y]; exact Nat.mod_lt _ (by omega_arith)⟩

/-- The exponentiation leaks the same in runs that agree on the public data. -/
theorem mrExpLoop_ct (M : Mont) : RelCT isa (Two ExpPre) (seqs (mrExpLoop M.mm)) fun _ _ => True := by
  rw [mrExpLoop_eq]
  refine RelCT.seqs_app (by simp) (by simp [mrLast]) (RelCT.seq (R := Two LastW) ?_ ?_)
  · simp only [seqs]
    refine RelCT.seq (kt_piece (fun q : EPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i q.u) [] (by decide)
      (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) ?_)
      ((words_ct M).mono (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => wordL_lastW h) h)
    rintro q s ⟨hk, hp, hd, mi, c, bm, b, hc, hT, hE, hodd, hc1, hY⟩
    exact WP.mono (expStart_ok hd hc hT hY) fun t hI =>
      ⟨by have := hd.w4; omega_using [this], mi, c, bm, b, s, ⟨hk, hp.hdr, hp.wr, hd⟩, hE, hI, hodd, hc1⟩
  · refine RelCT.seqs_app (by simp [mrLast]) (by simp [mrLast]) (RelCT.seq (mrLast_ct M (Or.inl rfl)) ?_)
    refine RelCT.seqs_app (by simp [mrLast]) (by simp [mrLast]) (RelCT.seq (mrLast_ct M (Or.inr (Or.inl rfl))) ?_)
    exact (mrLast_ct M (Or.inr (Or.inr rfl))).mono (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.RsaKeyGen.X86_64

end

end

/-!
# A candidate on x86-64: constant time of a round of Miller–Rabin

A round, from what it needs (`R0`), for runs that agree on the
public data, the witness passing or not among them (`RPub.pass`): its
witness, the witness in Montgomery form, the exponentiation, and the end,
which branches on the flag. Between the pieces, what each run keeps is
little (the header, `Good`); the facts that make the next pieces run come
from the correctness lemmas of whole stretches.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- An entry of `MrPub.vs`. -/
tactic_template "mem_vs" : tactic => `(tactic| plain_simp_names first
                   | (simp only [MrPub.vs, List.mem_cons, true_or]; done)
                   | simp only [MrPub.vs, List.mem_cons, true_or, or_true])

/-- The header words of `MrH`, from `HP`. -/
theorem HP.mrh {p : MrPub} {i u : Nat} {ex : List (Nat × BitVec 64)} {s : State}
    (h : HP p.B p.wr (p.vs i u ++ ex) s) : MrH p i u s.mem :=
  ⟨h.hdr (kOut, p.op) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kLen, BitVec.ofNat 64 (8 * p.w)) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kUsedP, p.up) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kRand, p.rP) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kRandLen, BitVec.ofNat 64 p.rl) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kChecks, BitVec.ofNat 64 p.ch) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kI, BitVec.ofNat 64 i) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kUsed, BitVec.ofNat 64 u) (List.mem_append_left _ (by mem_vs))⟩

theorem hp0 {p : MrPub} {i u : Nat} {s : State} (h : HP p.B p.wr (p.vs i u) s) :
    HP p.B p.wr (p.vs i u ++ []) s := by rw [List.append_nil]; exact h

/-- `HP` after changes to the arrays and the header words `ks` outside `MrH`,
and `kUsed` to `u'`. -/
theorem hp_used {p : MrPub} {i u u' : Nat} {s t : State} {mi : BitVec 64} {rs : List (Nat × Nat)}
    (h : HP p.B p.wr (p.vs i u) s) (hg : Good t p.B p.Z p.w mi) (hw : t.wr = s.wr)
    (hf : Frm p.B rs s.mem t.mem)
    (hd : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], ∀ r ∈ rs, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k)
    (hu : word t.mem p.B (8 * kUsed) = BitVec.ofNat 64 u') : HP p.B p.wr (p.vs i u') t := by
  have hm := (hp0 h).mrh
  have e : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], word t.mem p.B (8 * k) = word s.mem p.B (8 * k) :=
    fun k hk => hf.word_eq (hd k hk) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have := mr_hp (ex := []) hg (hw.trans h.wr) ⟨(e _ (by simp)).trans hm.out, (e _ (by simp)).trans hm.len,
    (e _ (by simp)).trans hm.usedP, (e _ (by simp)).trans hm.rand, (e _ (by simp)).trans hm.rlen,
    (e _ (by simp)).trans hm.chk, (e _ (by simp)).trans hm.ki, hu⟩ (by simp)
  rwa [List.append_nil] at this

/-- The public data of a round: the witnesses so far plus one, the octets
read, and whether the witness passes. -/
structure RPub where
  p : MrPub
  i : Nat
  u : Nat
  pass : Bool

/-- What a round needs. -/
def R0 (q : RPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i q.u) s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (c bm : Nat) (r : List Byte) (uni : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧
      ECtx s.mem q.p.B q.p.w c ∧
      wv s.mem q.p.B (slot q.p.w aR2) q.p.w = 2 ^ (64 * q.p.w) * 2 ^ (64 * q.p.w) % c ∧ 1 < c ∧
      VG.Proof.RsaKeyGen.PrimeShape (64 * q.p.w) c ∧ Src s q.p.B q.p.Z q.p.rP r ∧ r.length = q.p.rl ∧
      q.u + 8 * q.p.w ≤ r.length ∧ word s.mem q.p.B (8 * kUni) = BitVec.ofNat 64 uni ∧ q.i < 2 ^ 61 ∧
      uni < 2 ^ 61 ∧ q.p.ch < 2 ^ 62 ∧ passOf c q.p.w q.u r = q.pass

/-- After the witness's octets. -/
def W1 (q : RPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i (q.u + 8 * q.p.w)) s

theorem midRanges_mrh (w : Nat) : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI],
    ∀ r ∈ preRanges w ++ expRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  have h : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], 8 * k + 8 ≤ VG.Impl.Bignum.hdrBytes ∧
      ∀ h ∈ ([(200, 8), (240, 8), (208, 8), (224, 8)] ++ [(248, 8), (176, 8), (208, 8), (224, 8), (216, 8)] :
        List (Nat × Nat)), 8 * k + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * k := by
    decide
  exact fun k hk => VG.Proof.RsaKeyGen.hdr_of_shape
    (VG.Proof.RsaKeyGen.shape_append (preRanges_shape w) (expRanges_shape w)) (h k hk).1 (h k hk).2

theorem witRanges_mrh (w : Nat) :
    ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], ∀ r ∈ witRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k :=
  fun k hk r hr => midRanges_mrh w k hk r
    (List.mem_append_left _ (by unfold preRanges; exact List.mem_append_left _ (List.mem_append_left _ hr)))

/-- After the witness: what its Montgomery form needs. -/
def W2 (q : RPub) (s : State) : Prop :=
  W1 q s ∧ MrDims q.p.B q.p.Z q.p.w ∧ ∃ (mi : BitVec 64) (c bm : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧
    wv s.mem q.p.B (slot q.p.w aR2) q.p.w = 2 ^ (64 * q.p.w) * 2 ^ (64 * q.p.w) % c ∧ c % 2 = 1 ∧ 1 < c

/-- The witness leaks the same in runs that agree on the public data. -/
theorem mrWitness_ct : RelCT isa (Two R0) (seqs mrWitness) (Two W2) := by
  rw [mrWitness_eq]
  refine two_post (RelCT.seqs_app (by simp) (by simp) (RelCT.seq (R := Two W1) ?_ ?_)) ?_
  · simp only [seqs]
    refine kt_piece (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i q.u) [] (by decide)
      (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) ?_
    rintro q s ⟨hk, hp, hd, mi, c, bm, r, uni, hc, -, -, -, -, hsrc, -, hlen, -⟩
    have hm := (hp0 hp).mrh
    have hw4 := hd.w4
    refine WP.mono (witLoad_ok hc.good hd.z (by omega_arith) (by have := hd.w128; omega_arith) hm.rand hm.used hm.len
      (VG.Proof.RsaKeyGen.X86_64.Src.seg hsrc hlen) (by
        simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_arith))
      fun t ⟨_, hu, hf, hg, k⟩ => ⟨hk, hp_used hp hg k.2.2 hf (by rng_disj) hu⟩
  · exact kt_ct (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) [] (by decide)
      (fun q => vs_fst0 _ _ _) (fun _ _ h => h) (pins_nil _) (by taint_decide)
  · rintro q s ⟨hk, hp, hd, mi, c, bm, r, uni, hc, -, hR2, hc1, hsh, hsrc, -, hlen, -⟩
    have hm := (hp0 hp).mrh
    have hw4 := hd.w4
    obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_arith) hsh
    refine WP.mono (mrWitness_ok hd hc hsh.1 hb hm.rand hm.used hm.len (VG.Proof.RsaKeyGen.X86_64.Src.seg hsrc hlen) (by
        simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_arith))
      fun t ⟨hc', _, _, hu, hf, k⟩ => ⟨⟨hk, hp_used hp hc'.good k.2.2 hf (witRanges_mrh _) hu⟩, hd, mi, c, _, hc', ?_,
        hsh.1, hc1⟩
    rw [hf.wv_eq (d := slot q.p.w aR2) (k := q.p.w) (by simp only [witRanges]; rng_disj)
      (by have := hc.good.scr.nowrap; have := slot_le (w := q.p.w) (show aR2 < 8 by decide); have := hd.z; omega_arith), hR2]

/-- After the witness's Montgomery form. -/
def W3 (q : RPub) (s : State) : Prop :=
  W1 q s ∧ MrDims q.p.B q.p.Z q.p.w ∧ ∃ (mi : BitVec 64) (c bm b : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧
    wv s.mem q.p.B (slot q.p.w aXm) q.p.w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * q.p.w) % c ∧ c % 2 = 1 ∧ 1 < c

/-- The table's public header words: the entry pointer and the count. -/
abbrev RPub.tvs (q : RPub) (j : Nat) : List (Nat × BitVec 64) :=
  q.p.vs q.i (q.u + 8 * q.p.w) ++ [(kV, off q.p.B (slot q.p.w (8 + (j + 2)))), (kBits, BitVec.ofNat 64 (14 - j))]

theorem RPub.tvs_fst (q : RPub) (j : Nat) : (q.tvs j).map (·.1) = mrS ++ [kV, kBits] := q.p.vs_fst _ _ _

/-- Within the table's loop: the header, and what a multiplication `y := y T_1`
needs. -/
def TLW (p : RPub × Nat) (s : State) : Prop :=
  KW p.1.p.B p.1.p.wr ∧ HP p.1.p.B p.1.p.wr (p.1.tvs p.2) s ∧ MrDims p.1.p.B p.1.p.Z p.1.p.w ∧ p.2 < 14 ∧
    ∃ (mi : BitVec 64) (c bm : Nat), MrCtx s p.1.p.B p.1.p.Z p.1.p.w mi c bm ∧
      wv s.mem p.1.p.B (slot p.1.p.w aXm) p.1.p.w < c

theorem tvs_lt (q : RPub) (j : Nat) : ∀ e ∈ q.tvs j, e.1 < 32 :=
  q.p.vs_lt _ _ _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; decide)

/-- `y := y T_1` keeps `TLW`. -/
theorem tlw_mm (M : Mont) {p : RPub × Nat} {s : State} (h : TLW p s) : WP isa (M.mm aY aY aXm) s (TLW p) := by
  obtain ⟨hk, hp, hd, hj, mi, c, bm, hc, hx⟩ := h
  have hw' : p.1.p.w < 2 ^ 31 := by have := hd.w128; omega_arith
  refine WP.mono (M.mm_ok hc.good hd.z (by have := hd.w4; omega_arith) hw' (o := aY) (a := aY) (b := aXm) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv (by rw [hc.n]; exact hx))
    fun t ⟨hg, _, _, ha', k⟩ => ?_
  have hf : Frm p.1.p.B [(slot p.1.p.w aAcc, 8 * (p.1.p.w + 2)), (slot p.1.p.w aTmp, 8 * (p.1.p.w + 2)),
      (slot p.1.p.w aY, 8 * (p.1.p.w + 2))] s.mem t.mem := Frm.of_arrays ha' (by simp)
  refine ⟨hk, hp.frm hf ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) (tvs_lt _ _) hg.rdi k.2.2, hd, hj, mi, c, bm,
    hc.of_frm hd hf hg.scr hg.rdi ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl), ?_⟩
  rw [hf.wv_eq (d := slot p.1.p.w aXm) (k := p.1.p.w) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl)
    (by have := hc.good.scr.nowrap; have := slot_le (w := p.1.p.w) (show aXm < 8 by decide); have := hd.z; omega_arith)]
  exact hx

/-- The copy of `y` into entry `j + 2`, at `kV`. -/
theorem tabCopy_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm j : Nat} (hd : MrDims B Z w)
    (hc : MrCtx s B Z w mi c bm) (hj : j < 14) (hV : word s.mem B (8 * kV) = off B (slot w (8 + (j + 2)))) :
    WP isa (seqs [.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))],
      copyWords]) s fun t => MrCtx t B Z w mi c bm ∧
      wv t.mem B (slot w aXm) w = wv s.mem B (slot w aXm) w ∧ Frm B [(slot w 8, tabBytes w)] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hg := hc.good
  have hn := hg.scr.nowrap
  have hZ := hd.z
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hE := ent_in_tab w (e := j + 2) (by omega_arith)
  have hte := tab_end w
  have haE := aE_fits hd
  have hY8 := slot_le (w := w) (show aY < 8 by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = off B (slot w aY) ∧ t.gpr .rbx = off B (slot w (8 + (j + 2))) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aY) (by decide), hl kV (by decide), hg.hdr.hw,
      hg.hdr.harr aY (by decide), hV]) rfl) fun s₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (copyB_ok (hg.scr.congr k₁.2.2) hsi hbx h12 (by have := hd.w4; omega_arith) hw' (by omega_arith)
    (by omega_arith) (Or.inr (by omega_arith))) fun t ⟨_, ho, k⟩ => ?_
  rw [hm₁] at ho
  have hf : Frm B [(slot w 8, tabBytes w)] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot w 8) (n' := tabBytes w) hE.1 (by omega_arith)) (by simp)
  have hdi : t.gpr .rdi = B := (k.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  have h8 : 256 ≤ slot w 8 := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega_arith
  have hgt : Good t B Z w mi := ⟨hg.scr.congr (k.2.2.trans k₁.2.2), hdi, Hdr.of_frm hg.hdr hf (by simp; omega_arith)⟩
  have hN8 := slot_le (w := w) (show aN < 8 by decide)
  have hX8 := slot_le (w := w) (show aXm < 8 by decide)
  have hR1 := slot_mono w (show aE ≤ aR1 by decide)
  have hRm := slot_mono w (show aE ≤ aRm1 by decide)
  have h1s := slot_succ w aR1
  have h1m : slot w (aR1 + 1) = slot w aRm1 := rfl
  have hx' := hd.x
  have hBs : slot w aB = slot w 8 + 8 * (w + 2) := slot_succ w 8
  have h10 : slot w 8 + 2 * (8 * (w + 2)) ≤ slot w (8 + (j + 2)) := by
    rw [show 8 + (j + 2) = 8 + (2 + j) by omega_arith, slot_add_mul, Nat.add_mul]; omega_arith
  have lo : ∀ {d : Nat}, d + 8 * w ≤ slot w 8 →
      ∀ r ∈ [(slot w 8, tabBytes w)], d + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d hd' r hr; simp only [List.mem_singleton] at hr; subst hr; exact Or.inl hd'
  have hi : ∀ {d : Nat}, slot w aE ≤ d → ∀ r ∈ [(slot w 8, tabBytes w)], d + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d hd' r hr; simp only [List.mem_singleton] at hr; subst hr; right; dsimp only; omega_arith
  refine ⟨⟨hgt, ?_, ?_, ?_, ?_, ?_⟩, ?_, hf, (k₁.trans k).mono (by decide)⟩
  · rw [hf.word_eq (d := slot w aN) (fun r hr => by
      have := lo (d := slot w aN) (by omega_arith) r hr; have := hd.w4; omega_arith) (by omega_arith)]
    exact hc.inv
  · rw [hf.wv_eq (lo (by omega_arith)) (by omega_arith)]; exact hc.n
  · rw [ho.wv (Or.inl (by omega_arith)) (by omega_arith)]; exact hc.b
  · rw [hf.wv_eq (hi hR1) (by omega_arith)]; exact hc.r1
  · rw [hf.wv_eq (hi hRm) (by omega_arith)]; exact hc.rm1
  · exact hf.wv_eq (lo (by omega_arith)) (by omega_arith)

/-- The copy of `y` into the entry keeps `TLW`. -/
theorem tlw_copy {p : RPub × Nat} {s : State} (h : TLW p s) :
    WP isa (seqs [.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))],
      copyWords]) s (TLW p) := by
  obtain ⟨hk, hp, hd, hj, mi, c, bm, hc, hx⟩ := h
  have hmem : (kV, off p.1.p.B (slot p.1.p.w (8 + (p.2 + 2)))) ∈ p.1.tvs p.2 := by
    unfold RPub.tvs; exact List.mem_append_right _ List.mem_cons_self
  have hV := hp.hdr _ hmem
  dsimp only at hV
  have h8 := hdr_lt_slot p.1.p.w 8 (show 31 < 32 by decide)
  refine WP.mono (tabCopy_ok hd hc hj hV) fun t ⟨hct, hxt, hf, k⟩ => ⟨hk, hp.frm hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; dsimp only; omega_arith) (tvs_lt _ _) hct.good.rdi k.2.2, hd, hj, mi, c,
    bm, hct, by rw [hxt]; exact hx⟩

/-- At iteration `j` of the table's loop, from `s₀` where it starts. -/
def TL (p : RPub × Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (c bm b : Nat) (s₀ : State), KW p.1.p.B p.1.p.wr ∧
    (∀ e ∈ p.1.p.vs p.1.i (p.1.u + 8 * p.1.p.w), word s₀.mem p.1.p.B (8 * e.1) = e.2) ∧ s₀.wr = p.1.p.wr ∧
    MrDims p.1.p.B p.1.p.Z p.1.p.w ∧ TabI p.1.p.B p.1.p.Z p.1.p.w mi c bm b s₀ p.2 s ∧ c % 2 = 1 ∧ 1 < c

theorem mrS_tab (w : Nat) : ∀ j ∈ mrS, ∀ r ∈ tabRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  have h : ∀ j ∈ mrS, 8 * j + 8 ≤ VG.Impl.Bignum.hdrBytes ∧
      ∀ h ∈ ([(208, 8), (224, 8)] : List (Nat × Nat)), 8 * j + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * j := by
    decide
  exact fun j hj => VG.Proof.RsaKeyGen.hdr_of_shape (tabRanges_shape w) (h j hj).1 (h j hj).2

theorem vs_tab (p : MrPub) (i u : Nat) :
    ∀ e ∈ p.vs i u, e.1 < 32 ∧ ∀ r ∈ tabRanges p.w, 8 * e.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * e.1 := fun e he => by
  have h1 : e.1 ∈ mrS := by
    have := List.mem_map_of_mem (f := (·.1)) he
    rwa [show (p.vs i u).map (·.1) = mrS by simp only [MrPub.vs, mrS, List.map_cons, List.map_nil]] at this
  have h2 : ∀ j ∈ mrS, j < 32 := by decide
  exact ⟨h2 _ h1, mrS_tab p.w _ h1⟩

theorem tl_hp {p : RPub × Nat} {s : State} (h : TL p s) : HP p.1.p.B p.1.p.wr (p.1.tvs p.2) s := by
  obtain ⟨mi, c, bm, b, s₀, -, hh, hw, -, hI, -⟩ := h
  refine ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hdr_frm hI.frm (vs_tab _ _ _) hh e he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hI.v
    · exact hI.bits

theorem tl_hp0 {p : RPub × Nat} {s : State} (h : TL p s) :
    HP p.1.p.B p.1.p.wr (p.1.p.vs p.1.i (p.1.u + 8 * p.1.p.w)) s := by
  obtain ⟨mi, c, bm, b, s₀, -, hh, hw, -, hI, -⟩ := h
  exact ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => hdr_frm hI.frm (vs_tab _ _ _) hh e he⟩

theorem tl_tlw {p : RPub × Nat} {s : State} (h : TL p s) (hj : p.2 < 14) : TLW p s := by
  have hp := tl_hp h
  obtain ⟨mi, c, bm, b, s₀, hk, -, -, hd, hI, -, hc1⟩ := h
  exact ⟨hk, hp, hd, hj, mi, c, bm, hI.ctx, by rw [hI.xm]; exact Nat.mod_lt _ (by omega_arith)⟩

/-- The table's loop leaks the same in runs that agree on the public data. -/
theorem tabLoop_ct (M : Mont) :
    RelCT isa (Two fun (q : RPub) s => 0 < 14 ∧ TL (q, 0) s)
      (.loop (seqs [M.mm aY aY aXm,
        .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))], copyWords,
        .block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2), .alu .add .rdx (.reg .rdx),
          .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx), .store (hdr kV) .rax,
          .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]) .ne)
      (Two fun q s => TL (q, 14) s) := by
  refine two_loop (Φ := fun q j s => TL (q, j) s) (fun _ => 14) ?_ ?_
  · simp only [seqs]
    refine RelCT.seq (R := Two TLW) (two_post (two_map (fun p : RPub × Nat => (⟨p.1.p.B, p.1.p.Z, p.1.p.w⟩ : Ws))
      (fun _ _ h => let ⟨_, _, hd, _, mi, _, _, hc, _⟩ := tl_tlw h.2 h.1; ⟨mi, hc.good, hd.z⟩)
      (M.ct (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))) fun p s h => tlw_mm M (tl_tlw h.2 h.1)) ?_
    refine RelCT.assoc (RelCT.seq (R := Two TLW)
      (kt_piece (fun p : RPub × Nat => p.1.p.B) (fun p => p.1.p.wr) (mrS ++ [kV, kBits]) (fun p => p.1.tvs p.2) []
        (by decide) (fun p => p.1.tvs_fst p.2) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide)
        fun _ _ h => tlw_copy h)
      (kt_ct (fun p : RPub × Nat => p.1.p.B) (fun p => p.1.p.wr) (mrS ++ [kV, kBits]) (fun p => p.1.tvs p.2) []
        (by decide) (fun p => p.1.tvs_fst p.2) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide)))
  · rintro q j s hj ⟨mi, c, bm, b, s₀, hk, hh, hw, hd, hI, hodd, hc1⟩
    refine WP.mono (tabStep_ok M hd hodd hc1 hj hI) fun t ⟨hz, hI'⟩ => ⟨?_, fun _ => ?_, fun _ => ?_⟩
    · simp only [eval, hz, Option.map_some, Option.some.injEq]
      by_cases h : j + 1 = 14 <;> simp [h]; omega_arith
    · exact ⟨mi, c, bm, b, s₀, hk, hh, hw, hd, hI', hodd, hc1⟩
    · rename_i e; rw [← e]; exact ⟨mi, c, bm, b, s₀, hk, hh, hw, hd, hI', hodd, hc1⟩

/-- The table leaks the same in runs that agree on the public data. -/
theorem tabBuild_ct (M : Mont) : RelCT isa (Two W3) (seqs (tabBuild M.mm)) fun _ _ => True := by
  rw [tabBuild_eq]
  refine RelCT.seqs_app (by simp) (by simp) (RelCT.seq (R := Two fun (q : RPub) s => 0 < 14 ∧ TL (q, 0) s) ?_ ?_)
  · simp only [seqs]
    refine kt_piece (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) []
      (by decide) (fun q => vs_fst0 _ _ _) (fun _ _ h => h.1) (pins_nil _) (by taint_decide) ?_
    rintro q s ⟨⟨hk, hp⟩, hd, mi, c, bm, b, hc, hX, hodd, hc1⟩
    exact WP.mono (tabHead_ok hd hc hc1 hX) fun t ⟨hI, hf, k⟩ => ⟨by decide, mi, c, _, b, t, hk,
      fun e he => by rw [← hI.frm.word_eq (by have := vs_tab _ _ _ e he; exact this.2) (by
        have := (vs_tab _ _ _ e he).1; omega_arith)]; exact hdr_frm hf (vs_tab _ _ _) hp.hdr e he,
      (hI.keep.2.2.symm.trans (k.2.2.trans hp.wr)), hd, hI, hodd, hc1⟩
  · refine RelCT.seqs_app (by simp) (by simp) (RelCT.seq (tabLoop_ct M) ?_)
    exact kt_ct (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) []
      (by decide) (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨let ⟨_, _, _, _, _, hk, _⟩ := h; hk, tl_hp0 h⟩)
      (pins_nil _) (by taint_decide)

/-- After the exponentiation: the flag, the witness passing or not. -/
def Rmid (q : RPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i (q.u + 8 * q.p.w)) s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (uni : Nat) (u : Bool), Good s q.p.B q.p.Z q.p.w mi ∧
      word s.mem q.p.B (8 * kFlag) = mask q.pass ∧ word s.mem q.p.B (8 * kUni) = BitVec.ofNat 64 uni ∧
      word s.mem q.p.B (8 * kU) = mask u ∧ uni < 2 ^ 61

/-- The test of the flag. -/
theorem flagTest_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {f : Bool} (hF : word s.mem B (8 * kFlag) = mask f) :
    WP isa (.block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (!f) ∧ t.mem = s.mem ∧ Keep [.rcx, .rax] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kFlag)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show kFlag < 32 by decide); omega_arith)
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t => t.zf = some (!f) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hF, BitVec.and_self]
    cases f <;> decide) rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩

/-- The end of the round leaks the same in runs that agree on the public
data, the witness passing or not among them. -/
theorem roundTail_ct : RelCT isa (Two Rmid) (seqs [
      .block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)],
      .ite .e (.block [])
        (.block [.mov .rax (.mem (hdr kI)), .alu .add .rax (.imm 1), .store (hdr kI) .rax,
          .mov .rdx (.mem (hdr kU)), .alu .and .rdx (.imm 1), .alu .add .rdx (.mem (hdr kUni)), .store (hdr kUni) .rdx,
          .alu .cmp .rax (.imm 17), .alu .sbb .rcx (.reg .rcx), .alu .cmp .rdx (.mem (hdr kChecks)),
          .alu .sbb .rax (.reg .rax), .alu .or .rcx (.reg .rax), .alu .and .rcx (.imm 3), .alu .add .rcx (.imm 1)]),
      .block [.store (hdr kStat) .rcx]]) fun _ _ => True := by
  simp only [seqs]
  refine RelCT.seq (R := Two fun (q : RPub) s => (KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i (q.u + 8 * q.p.w)) s) ∧
      s.zf = some (!q.pass))
    (kt_piece (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) [] (by decide)
      (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) ?_)
    (two_ite_seq (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2])
      (kt_ct (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) [] (by decide)
        (fun q => vs_fst0 _ _ _) (fun _ _ h => h.1.1) (pins_nil _) (by taint_decide))
      (kt_ct (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) [] (by decide)
        (fun q => vs_fst0 _ _ _) (fun _ _ h => h.1.1) (pins_nil _) (by taint_decide)))
  rintro q s ⟨hk, hp, hd, mi, uni, u, hg, hF, -⟩
  exact WP.mono (flagTest_ok hg hd.z hF) fun t ⟨hz, hm, k⟩ =>
    ⟨⟨hk, ⟨(k.gpr (by decide)).trans hp.rdi, k.2.2.trans hp.wr, fun e he => by rw [hm]; exact hp.hdr e he⟩⟩, hz⟩

end VG.Proof.RsaKeyGen.X86_64
