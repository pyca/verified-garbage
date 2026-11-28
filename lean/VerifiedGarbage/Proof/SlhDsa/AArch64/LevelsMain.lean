module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.LevelsHeight
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.Lemmas

-- separate module: `LevelsCT` runs the taint analysis, which needs a `meta import` of each of its imports;
-- keeping the correctness proofs here keeps them out of that.

/-!
# SLH-DSA on AArch64: `levels` meets its contract

As on x86-64 (`Proof/SlhDsa/X86_64/LevelsMain.lean`): the loop of the
heights (`heights_ok`), the restore of the caller's registers, and the whole
function (`levels_correct`): from a state satisfying `levelsContract`'s
precondition, it returns in a state satisfying its postcondition, keeping
what the calling convention keeps.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Levels

open VG VG.AArch64 VG.AArch64.Steps VG.Proof.SlhDsa.AArch64.Blocks VG.Proof.SlhDsa.AArch64.Wots4
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64

variable {p : Params} {σ : State} {S AU : Addr} {idx c h z₀ : Nat} {pkSeed a16 : List Byte}

/-! ## The heights -/

theorem pow_eq_one {k : Nat} : 2 ^ k = 1 ↔ k = 0 := by
  constructor
  · intro e; rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · have := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp h); omega_using [this, e]
  · intro e; rw [e]

theorem heights_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {u : State} (hI : HI hE 0 u) :
    WP isa (.loop (Tree.heightBody ⟨p.n, p.len⟩ name T.code) (.nonzero .x .x9)) u (HI hE h) := by
  have hh := hE.h_le
  have h1 := hE.h_pos
  refine WP.loop (M := isa) (Inv := fun m v => ∃ r, m = h - r ∧ r < h ∧ HI hE r v) (fun m v hv => ?_) h u
    ⟨0, by omega_using [], by omega_using [h1], hI⟩
  obtain ⟨r, rfl, hr, hv⟩ := hv
  refine WP.mono (height_ok hE hz T name hr hv) fun v' ⟨hv', h9⟩ => ?_
  have hp : 2 ^ (h - (r + 1)) < 2 ^ 64 := by
    have := pow_lt (h := h) (r := r + 1) (by omega_using [hh]); omega_using [this]
  have ev := eval_nz h9 hp (by decide)
  by_cases e : r + 1 = h
  · subst e
    exact Or.inl ⟨by rw [ev, decide_eq_true (pow_eq_one.mpr (by omega_using []))]; rfl, hv'⟩
  · exact Or.inr ⟨by rw [ev, decide_eq_false (fun h' => e (by have := pow_eq_one.mp h'; omega_using [this, hr]))]; rfl,
      h - (r + 1), by omega_using [hr, e], r + 1, rfl, by omega_using [hr, e], hv'⟩

/-! ## The epilogue -/

theorem restore_eq3 : restoreRegs 3 Tree.saved = [.ldr .x .x20 .x19 1416, .ldr .x .x21 .x19 1424, .ldr .x .x22 .x19 1432, .ldr .x .x23 .x19 1440, .ldr .x .x24 .x19 1448, .ldr .x .x25 .x19 1456, .ldr .x .x26 .x19 1464, .ldr .x .x27 .x19 1472, .ldr .x .x30 .x19 1480, .ldr .x .x19 .x19 1408] := rfl

theorem restore_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) {t : State} (hb : Base hE t) {Q : State → Prop}
    (k : ∀ t', t'.mem = t.mem → t'.sp = t.sp → VK t' t → (∀ r ∈ preserved, t'.gpr r = σ.gpr r) → Q t') :
    WP isa (.block (restoreRegs 3 Tree.saved)) t Q := by
  have hin : ∀ i < 10, InRegions (t.rd ++ t.wr) (at' S (Layout.oSave 3 i)) 8 := fun i hi =>
    hE.inScr' hb.wr (by rw [oSave3_eq]; omega_using [hi])
  rw [restore_eq3]
  refine wp_vk rfl ?_
  refine wp_ldr (a := at' S (Layout.oSave 3 1)) ⟨by decide, by decide⟩ (by rw [hb.x19]; rfl) (by exact hin 1 (by decide)) fun t1 u1 => ?_
  refine wp_ldr (a := at' S (Layout.oSave 3 2)) ⟨by decide, by decide⟩ (by rw [u1.other _ (by decide), hb.x19]; rfl) (by rw [u1.rd, u1.wr]; exact hin 2 (by decide)) fun t2 u2 => ?_
  refine wp_ldr (a := at' S (Layout.oSave 3 3)) ⟨by decide, by decide⟩ (by rw [u2.other _ (by decide), u1.other _ (by decide), hb.x19]; rfl) (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hin 3 (by decide)) fun t3 u3 => ?_
  refine wp_ldr (a := at' S (Layout.oSave 3 4)) ⟨by decide, by decide⟩ (by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hb.x19]; rfl) (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin 4 (by decide)) fun t4 u4 => ?_
  refine wp_ldr (a := at' S (Layout.oSave 3 5)) ⟨by decide, by decide⟩ (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hb.x19]; rfl) (by rw [u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin 5 (by decide)) fun t5 u5 => ?_
  refine wp_ldr (a := at' S (Layout.oSave 3 6)) ⟨by decide, by decide⟩ (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hb.x19]; rfl) (by rw [u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin 6 (by decide)) fun t6 u6 => ?_
  refine wp_ldr (a := at' S (Layout.oSave 3 7)) ⟨by decide, by decide⟩ (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hb.x19]; rfl) (by rw [u6.rd, u6.wr, u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin 7 (by decide)) fun t7 u7 => ?_
  refine wp_ldr (a := at' S (Layout.oSave 3 8)) ⟨by decide, by decide⟩ (by rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hb.x19]; rfl) (by rw [u7.rd, u7.wr, u6.rd, u6.wr, u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin 8 (by decide)) fun t8 u8 => ?_
  refine wp_ldr (a := at' S (Layout.oSave 3 9)) ⟨by decide, by decide⟩ (by rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hb.x19]; rfl) (by rw [u8.rd, u8.wr, u7.rd, u7.wr, u6.rd, u6.wr, u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin 9 (by decide)) fun t9 u9 => ?_
  refine wp_ldr (a := at' S (Layout.oSave 3 0)) ⟨by decide, by decide⟩ (by rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hb.x19]; rfl) (by rw [u9.rd, u9.wr, u8.rd, u8.wr, u7.rd, u7.wr, u6.rd, u6.wr, u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin 0 (by decide)) fun t10 u10 => ?_
  refine WP.block_nil fun hvk => ?_
  have hm1 : t1.mem = t.mem := by rw [u1.mem]
  have hm2 : t2.mem = t.mem := by rw [u2.mem, u1.mem]
  have hm3 : t3.mem = t.mem := by rw [u3.mem, u2.mem, u1.mem]
  have hm4 : t4.mem = t.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have hm5 : t5.mem = t.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hm6 : t6.mem = t.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hm7 : t7.mem = t.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hm8 : t8.mem = t.mem := by rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hm9 : t9.mem = t.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hm10 : t10.mem = t.mem := by rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine k t10 hm10 (by rw [u10.sp, u9.sp, u8.sp, u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]) hvk fun r hr => ?_
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [u10.gpr, hm9]; exact hb.saved 0 (by decide)
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; exact hb.saved 1 (by decide)
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, hm1]; exact hb.saved 2 (by decide)
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, hm2]; exact hb.saved 3 (by decide)
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr, hm3]; exact hb.saved 4 (by decide)
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr, hm4]; exact hb.saved 5 (by decide)
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.gpr, hm5]; exact hb.saved 6 (by decide)
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.gpr, hm6]; exact hb.saved 7 (by decide)
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.gpr, hm7]; exact hb.saved 8 (by decide)
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hb.x28]
  · rw [u10.other _ (by decide), u9.gpr, hm8]; exact hb.saved 9 (by decide)

/-! ## The whole function -/

theorem getD_nodesAt (m : Mem) (a : Addr) {i : Nat} (hi : i < c) :
    (nodesAt p m a c).getD i [] = bytesAt m (a + BitVec.ofNat 64 (i * p.n)) p.n := by
  simp [nodesAt, List.getD_eq_getElem?_getD, hi]

/-- The heights' invariant at the first height, from the state after the alignment. -/
theorem hi0 (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) {u : State} (hs : SH hE z₀ u) : HI hE 0 u := by
  have hn := hz.n32
  have hcnt := hE.cnt
  have hfit := hE.nodes_fit
  refine ⟨hs.base, hs.vk, by rw [hs.x21, Nat.zero_mul, add0], by rw [hs.x22, Nat.add_zero], by rw [hs.x23, Nat.sub_zero, hcnt],
    by rw [hs.x25, Nat.add_zero], by rw [hs.x26, Nat.add_zero], by rw [hs.x27, Nat.add_zero], fun i hi => ?_, fun r' hr' => ?_⟩
  · have hic : i < c := by rw [hcnt]; omega_using [hi]
    have hf₁ := node_fit hE (i := i) (by omega_using [hic])
    rw [bytesAt_frame hs.fr (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact Entry.dscr (Or.inr (by rw [oN_eq]; omega_using [])) (by omega_using [hf₁]) (by decide)) (by omega_using [hn]),
      up, upNodes, L0, getD_nodesAt _ _ hic, ofNat_add']
  · rw [ite_eq_right (Nat.not_lt_zero _)]
    have hl : r' * p.n + p.n ≤ h * p.n := by
      have := Nat.mul_le_mul_right p.n (show r' + 1 ≤ h by omega_using [hr']); rwa [Nat.succ_mul] at this
    exact bytesAt_frame hs.fr (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hE.dAU hl (by rw [oSigTmp_eq]; decide)) (by omega_using [hn])

/-- What `levels` does, from the entry state `σ`. -/
structure LevelsPost (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (t : State) : Prop where
  cs : ∀ r ∈ preserved, t.gpr r = σ.gpr r
  sp : t.sp = σ.sp
  vk : VK t σ
  frame : Frame (lch p S AU c h) σ.mem t.mem
  env : Env p t.mem S pkSeed a16
  top : bytesAt t.mem (at' S Layout.oN) p.n = (up p σ S c z₀ pkSeed a16 h).getD 0 []
  auth : ∀ r < h, bytesAt t.mem (AU + BitVec.ofNat 64 (r * p.n)) p.n =
    xorB (oldA p σ AU r) (pick p.n (up p σ S c z₀ pkSeed a16 r) (capB σ S / 2 ^ (z₀ + r)) idx (z₀ + r))

theorem levels_wp (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    WP isa (Tree.levels ⟨p.n, p.len⟩ name T.code) σ (LevelsPost hE) := by
  refine WP.seq (WP.mono (pro_ok hE) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (align_ok hE h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (heights_ok hE hz T name (hi0 hE hz h₂)) fun t₃ h₃ => ?_)
  refine restore_ok hE h₃.base fun t₄ m₄ sp₄ vk₄ cs₄ => ⟨cs₄, by rw [sp₄]; exact h₃.base.sp, VK.trans vk₄ h₃.vk,
    by rw [m₄]; exact h₃.base.frame, by rw [m₄]; exact h₃.base.env hz, ?_, fun r hr => ?_⟩
  · have := h₃.nodes 0 (by rw [Nat.sub_self]; decide)
    rw [Nat.zero_mul, Nat.add_zero] at this
    rw [m₄]; exact this
  · rw [m₄, h₃.auth r hr, ite_eq_left hr]

/-- The entry facts of a state of the precondition. -/
theorem entry_of {s : State} (h : (levelsContract p).pre s) :
    ∃ pkSeed a16, Entry p s (s.gpr .x0) (s.gpr .x4) (s.gpr .x5).toNat (s.gpr .x2).toNat (heightsOf s) (s.gpr .x3).toNat
      pkSeed a16 := by
  obtain ⟨hreg, ⟨pkSeed, a16, henv⟩, hx1, h1, hle, hcnt, hcap, hidx, v0, v1, v2, v3⟩ := h
  exact ⟨pkSeed, a16, rfl, hx1, by simp, by simp, rfl, by simp, hreg, henv, h1, hle, hcnt, hcap, hidx, v0, v1, v2, v3⟩

/-- The first part of `Verified`: from every state of the precondition,
`levels` returns, keeping what the calling convention keeps, in a state of
the postcondition. -/
theorem levels_correct (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    ∀ s, (levelsContract p).pre s → ∃ t s', Exec isa (Tree.levels ⟨p.n, p.len⟩ name T.code) s t s' ∧
      abiPreserved s s' ∧ (levelsContract p).post s s' := by
  intro s hpre
  obtain ⟨pkSeed, a16, hE⟩ := entry_of hpre
  have hx1 := hE.x1
  obtain ⟨t, s', he, q⟩ := levels_wp hE hz T name
  refine ⟨t, s', he, ⟨q.cs, q.sp, q.vk⟩, ?_⟩
  intro pkSeed' a16' henv'
  have e₁ : pkSeed' = pkSeed := by rw [← henv'.seedA 0 (by decide), hE.env.seedA 0 (by decide)]
  have e₂ : a16' = a16 := by rw [← henv'.adrsA 0 (by decide), hE.env.adrsA 0 (by decide)]
  subst e₁ e₂
  refine ⟨q.env, ?_, fun r hr => ?_, ?_⟩
  · rw [hx1]; exact q.top
  · rw [q.auth r hr, hx1]
  · rw [hx1]; exact q.frame

end VG.Proof.SlhDsa.AArch64.Levels
