module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMr
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWin
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrTab
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMr
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWin
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrTab
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
meta import VerifiedGarbage.Proof.Bignum.CrtExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

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
