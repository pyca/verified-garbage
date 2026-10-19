module

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrExp
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTab
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTab
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Rsa.Ranges
meta import VerifiedGarbage.Proof.Rsa.Ranges

/-!
# A candidate on AArch64: constant time of Miller–Rabin's table

`tabBuild`, for runs that agree on the working space (`tabBuild_ct`): the
entry being written is a header word, pinned after the block that loads it
(`toEnt_ct`); its loop counts 14 entries, which correctness pins
(`tabStep_ok`); the multiplications are `Mont.ct`'s, with `[aXm]` below `c`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa (slot_lt)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- What the table's code keeps: the working space and its bounds, `c`, and
`[aXm]` below `c`. -/
def TB (L : WsP) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 128 ∧ slot L.w aE + 8 * (L.w + 2) ≤ L.Z ∧ ∃ c bm b, MrCtx s L.B L.Z L.w c bm ∧ c % 2 = 1 ∧
    1 < c ∧ wv s.mem L.B (slot L.w aXm) L.w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * L.w) % c

/-- `TB`, with entry `e` in `kV`. -/
def TBE (L : WsP) (e : Nat) (s : State) : Prop :=
  TB L s ∧ e < 16 ∧ word s.mem L.B (8 * kV) = off L.B (slot L.w (aT0 + e))

theorem TB.ws {L : WsP} {s : State} (h : TB L s) : Ws s L.B L.Z L.w := by
  obtain ⟨-, -, -, c, bm, b, hc, -⟩ := h; exact hc.ws

theorem TB.of_tab {L : WsP} {s t : State} (h : TB L s) {rs : List (Nat × Nat)} (hf : Frm L.B rs s.mem t.mem)
    (hs : ∀ r ∈ rs, r ∈ tabRanges L.w) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : TB L t := by
  obtain ⟨h4, h128, hEZ, c, bm, b, hc, hodd, hc1, hX⟩ := h
  have hn := hc.ws.scr.nowrap
  have hXZ := hc.ws.sl (show aXm < 16 by decide)
  have dX : ∀ r ∈ tabRanges L.w, slot L.w aXm + 8 * L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot L.w aXm := by
    unfold tabRanges; w_disj
  exact ⟨h4, h128, hEZ, c, bm, b, hc.of_tab hf hs k hr, hodd, hc1,
    by rw [hf.wv_eq (fun r hr' => dX r (hs r hr')) (by omega)]; exact hX⟩

/-- The registers pinned before an entry's copy. -/
def entVal (L : WsP) (a e : Nat) : Reg → BitVec 64
  | .x0 => L.B
  | .x12 => BitVec.ofNat 64 L.w
  | .x16 => off L.B (slot L.w a)
  | _ => off L.B (slot L.w (aT0 + e))

theorem toEntPre_ok {L : WsP} {e : Nat} {s : State} (h : TBE L e s) (a : Nat) :
    WP isa (.block (ws ++ base a .x16 ++ [ldh .x17 kV])) s fun t =>
      ∀ r ∈ [Reg.x0, .x12, .x16, .x17], t.gpr r = entVal L a e r := by
  obtain ⟨hT, he, hV⟩ := h
  have hw := hT.ws
  have hs := hw.scr
  have hn := hs.nowrap
  have h256 := hw.h256
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok a .x16 ((k₁.gpr .x0 (by decide)).trans hw.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.x17] (Q := fun t => t.gpr .x17 = off L.B (slot L.w (aT0 + e))) (by
    brun [(k12.gpr .x0 (by decide)).trans hw.x0, hdr_enc (show kV < 32 by decide),
      (hs.congr k12.wr).ld (d := 8 * kV) (by simp only [kV, kT0, sCnt, sFn]; omega),
      (by rw [m₂, m₁]; exact hV : word s₂.mem L.B (8 * kV) = off L.B (slot L.w (aT0 + e)))])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h17, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ((k12.trans k).gpr .x0 (by decide)).trans hw.x0
  · exact ((k₂.trans k).gpr .x12 (by decide)).trans h12
  · exact (k.gpr .x16 (by decide)).trans h16
  · exact h17

/-- `toEnt a`: the copy's addresses are pinned after its first block. -/
theorem toEnt_ct {α : Type} (L : α → WsP) (e : α → Nat) {a : Nat} (ha : a < aT0)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base a .x16 ++ [ldh .x17 kV])) hc).isSome = true) :
    RelCT isa (Two fun x s => TBE (L x) (e x) s) (seqs (toEnt a)) (Two fun x s => TBE (L x) (e x) s) := by
  have eq : seqs (toEnt a) = Code.seq (.block (ws ++ base a .x16 ++ [ldh .x17 kV])) copyWords := rfl
  rw [eq]
  refine pin_ct [.x0] [.x0, .x12, .x16, .x17] (fun x => entVal (L x) a (e x))
    (pins_ws' (fun x => (L x).B) (fun x => (L x).Z) (fun x => (L x).w) fun _ _ h => h.1.ws) ht
    (fun x s h => toEntPre_ok h a) (by taint_decide) fun x s h => ?_
  rw [← eq]
  obtain ⟨hT, he, hV⟩ := h
  have hw := hT.ws
  have hn := hw.scr.nowrap
  have hEZ := hT.2.2.1
  refine WP.mono (toEnt_ok hw hEZ ha he hV) fun t ⟨_, ho, k⟩ => ?_
  have hE := ent_in_tab (L x).w he
  have hf : Frm (L x).B [(slot (L x).w aT0, 128 * ((L x).w + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot (L x).w aT0) (n' := 128 * ((L x).w + 2)) hE.1 (by omega)) (by simp)
  exact ⟨hT.of_tab hf (by simp [tabRanges]) k (by decide), he,
    by rw [hf.word_eq (VG.Proof.RsaKeyGen.past_hdrW rfl) (by decide)]; exact hV⟩

/-! ## The table's start -/

theorem tabStart_ct : RelCT isa (Two TB) (.block (ws ++ base aT0 .x3 ++ [sth .x3 kV, movi .x3 14, sth .x3 kBits]))
    (Two fun L s => TBE L 0 s) := by
  rw [List.append_assoc]
  exact ws_block_ct (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h.ws)
    (by taint_decide) fun L s h => by
      rw [← List.append_assoc]
      refine WP.mono (tabStart_ok h.ws) fun t ⟨hm, k⟩ => ?_
      have hf : Frm L.B [(8 * kV, 8), (8 * kBits, 8)] s.mem t.mem := by
        rw [hm]
        exact (frm_hdr (show kV < 32 by decide) _ (by simp)).trans (frm_hdr (show kBits < 32 by decide) _ (by simp))
      exact ⟨h.of_tab hf (by simp [tabRanges]) k (by decide), by decide, by
        rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]; rfl⟩

theorem nextEnt_ct {e : Nat} (he : e + 1 < 16) :
    RelCT isa (Two fun L s => TBE L e s) (.block nextEnt) (Two fun L s => TBE L (e + 1) s) :=
  two_piece [.x0] (pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) fun _ _ h => h.1.ws)
    (by taint_decide) fun L s h => by
      obtain ⟨hT, -, hV⟩ := h
      refine WP.mono (nextEnt_ok hT.ws hV) fun t ⟨hm, k⟩ => ?_
      have hf : Frm L.B [(8 * kV, 8)] s.mem t.mem := by
        rw [hm]; exact frm_hdr (show kV < 32 by decide) _ (by simp)
      exact ⟨hT.of_tab hf (by simp [tabRanges]) k (by decide), he, by rw [hm, word_writeW_self, slot_succ]; rfl⟩

/-- The table's loop: after `i` entries. -/
def TL (L : WsP) (i : Nat) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 128 ∧ slot L.w aE + 8 * (L.w + 2) ≤ L.Z ∧ ∃ c bm b s₀, TabI L.B L.Z L.w c bm b s₀ i s ∧
    c % 2 = 1 ∧ 1 < c

theorem copyA_tct {α : Type} {Φ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base a .x16 ++ base o .x17)) copyWords)
      hc).isSome = true) :
    RelCT isa (Two Φ) (copyA o a) fun _ _ => True := by
  have e : copyA o a = .seq (.block (ws ++ (base a .x16 ++ base o .x17))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  refine (ws_ct (Ψ := fun _ _ => True) B Z w hws ht fun x s h => ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
  rw [← e]
  exact WP.mono (copyA_ok (hws x s h) ho ha hoa) fun _ _ => trivial

/-! ## The table's loop -/

theorem tabMul_ok (M : Mont) {L : WsP} {i : Nat} {s : State} (hi : i < 14) (h : TL L i s) :
    WP isa (M.mm aY aY aXm) s fun t => TBE L (i + 2) t := by
  obtain ⟨h4, h128, hEZ, c, bm, b, s₀, hI, hodd, hc1⟩ := h
  have hc := hI.ctx
  have hn := hc.ws.scr.nowrap
  have hX : wv s.mem L.B (slot L.w aXm) L.w < c := by rw [hI.xm]; exact Nat.mod_lt _ (by omega)
  refine WP.mono (M.mm_ok hc.good.1 hc.good.2 (by omega) (by omega) (o := aY) (a := aY) (b := aXm) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.n]; exact hX)) fun t ⟨_, _, _, ha, k⟩ => ?_
  have hf : Frm L.B [(slot L.w aAcc, 8 * (L.w + 2)), (slot L.w aTmp, 8 * (L.w + 2)),
      (slot L.w aY, 8 * (L.w + 2))] s.mem t.mem := Frm.of_arrays ha (by simp)
  have hT : TB L s := ⟨h4, h128, hEZ, c, bm, b, hc, hodd, hc1, hI.xm⟩
  exact ⟨hT.of_tab hf (by simp [tabRanges]) k (by decide), by omega,
    by rw [hf.word_eq ((VG.Proof.RsaKeyGen.mm_shape _ _).hdrW rfl rfl) (by decide)]; exact hI.v⟩

theorem tabMul_ct (M : Mont) : RelCT isa (Two fun (p : WsP × Nat) s => p.2 < 14 ∧ TL p.1 p.2 s) (M.mm aY aY aXm)
    (Two fun (p : WsP × Nat) s => TBE p.1 (p.2 + 2) s) :=
  two_post (two_map (fun p : WsP × Nat => p.1)
    (fun (p : WsP × Nat) (s : State) (h : p.2 < 14 ∧ TL p.1 p.2 s) => by
      obtain ⟨-, -, -, -, c, bm, b, s₀, hI, -⟩ := h; exact ⟨_, hI.ctx.good⟩)
    (M.ct (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))) fun p s h => tabMul_ok M h.1 h.2

/-- An entry of the table's loop. -/
theorem tabStep_ct (M : Mont) : RelCT isa (Two fun (p : WsP × Nat) s => p.2 < 14 ∧ TL p.1 p.2 s)
    (seqs (([M.mm aY aY aXm] : List (Prog isa)) ++ toEnt aY ++
      ([.block (nextEnt ++ ([ldh .x3 kBits, .subImm .x .x3 .x3 1, sth .x3 kBits] : List Instr))] : List (Prog isa))))
      fun _ _ => True := by
  rw [List.append_assoc]
  refine ct_app' (by simp) (by simp [toEnt]) (tabMul_ct M) (ct_app' (by simp [toEnt]) (by simp)
    (toEnt_ct (fun p : WsP × Nat => p.1) (fun p => p.2 + 2) (by decide) (by taint_decide)) (two_taint [.x0]
      (pins_ws' (Φ := fun (p : WsP × Nat) s => TBE p.1 (p.2 + 2) s) (fun p : WsP × Nat => p.1.B) (fun p => p.1.Z)
        (fun p => p.1.w) fun _ _ h => h.1.ws)
      (by taint_decide)))

/-- The table leaks the same in runs that agree on the working space. -/
theorem tabBuild_ct (M : Mont) : RelCT isa (Two TB) (seqs (tabBuild M.mm)) fun _ _ => True := by
  rw [tabBuild_eq]
  refine ct_app' (by simp [tabHead]) (by simp) (Ψ := fun L s => 0 < 14 ∧ TL L 0 s) ?_ ?_
  · refine two_post ?_ fun L s h => ?_
    · unfold tabHead
      refine ct_app' (by simp) (by simp [toEnt]) tabStart_ct ?_
      refine ct_app' (by simp [toEnt]) (by simp) (toEnt_ct id (fun _ => 0) (by decide) (by taint_decide)) ?_
      refine ct_app' (by simp) (by simp [toEnt]) (nextEnt_ct (by decide)) ?_
      refine ct_app' (by simp [toEnt]) (by simp) (toEnt_ct id (fun _ => 1) (by decide) (by taint_decide)) ?_
      refine RelCT.seq (nextEnt_ct (by decide)) ?_
      exact copyA_tct (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h.1.ws)
        (by decide) (by decide) (by decide) (by taint_decide)
    · obtain ⟨h4, h128, hEZ, c, bm, b, hc, hodd, hc1, hX⟩ := h
      exact WP.mono (tabHead_ok hEZ hc hc1 hX) fun t ⟨hI, _⟩ => ⟨by decide, h4, h128, hEZ, c, bm, b, t, hI, hodd, hc1⟩
  refine RelCT.seq (two_loop (Φ := TL) (Ψ := fun L s => Ws s L.B L.Z L.w) (fun _ => 14) (tabStep_ct M) ?_)
    (copyA_tct (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h)
      (by decide) (by decide) (by decide) (by taint_decide))
  rintro L i s hi ⟨h4, h128, hEZ, c, bm, b, s₀, hI, hodd, hc1⟩
  exact WP.mono (tabStep_ok M h128 hEZ hodd hc1 hi hI) fun t ⟨hI', hz⟩ =>
    ⟨eval_cnt .x3 hi hz, fun _ => ⟨h4, h128, hEZ, c, bm, b, s₀, hI', hodd, hc1⟩, fun _ => hI'.ctx.ws⟩


end VG.Proof.RsaKeyGen.AArch64
