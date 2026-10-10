import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Squeeze
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-!
# Calls of `vg_keccak_f1600_x2` on AArch64

Untrusted: everything here is checked by Lean. `call_ok`: a call (`X2.call`)
on the states at `p`, with the function's working space at `q` and the
return address kept in the 8 bytes after it (`callR`), permutes both states,
changes memory only in the states and `callR`, and keeps every register but
`x0`, `x1`, `x16` and `x17` (`x30` is reloaded), from the function's own
proof (`X2.correct`, by `WP.callV`). `squeeze_ok`: the
squeeze from memory that follows it in a caller (`X2.squeeze`).
-/

namespace VG.Proof.Sha3.AArch64.Neon.X2

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.X2 (code)
open VG.Proof.Sha3.AArch64 (Upd Mupd wp_ldr wp_str)
open VG.Spec.Sha3 (stateX2At keccakF)

/-- The registers a call may change. -/
def clobbered : List Reg := [.x0, .x1, .x16, .x17]

/-- What a call keeps. -/
structure CallKeep (s t : State) : Prop where
  gpr : ∀ r, r ∉ clobbered → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

/-- The caller's part of a call: the function's working space and the return address. -/
def callR (q : Addr) : Region := ⟨q, 136⟩

theorem code_writes (sha3 : Bool) : ∀ r, r ≠ .x16 → ∀ i ∈ instrs (code sha3), dstOf i ≠ some r := by
  have h : ∀ sha3, ((instrs (code sha3)).all fun i => dstOf i == none || dstOf i == some .x16) = true := by
    intro sha3; cases sha3 <;> (rw [← Code.allInstrs_eq]; lit_decide)
  intro r hr i hi he
  have := List.all_eq_true.mp (h sha3) i hi
  rw [he, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at this
  rcases this with h' | h'
  · exact absurd h' (Option.some_ne_none r)
  · exact hr (Option.some.inj h')

theorem code_noFrames (sha3 : Bool) : (code sha3).noFrames = true := by
  cases sha3 <;> lit_decide

/-- **A call** on the states at `p` (from `rp`), with the working space at `q` (`rb + off`). -/
theorem call_ok (sha3 : Bool) {s : State} {rp rb : Reg} {off : Nat} {p q : Addr}
    {A B : Spec.Sha3.State} (hoff : off < 8190) (hrp : rp ≠ .x1)
    (hp : s.gpr rp = p) (hq : s.gpr rb + BitVec.ofNat 64 off = q)
    (hpq : (pairR p).Disjoint (callR q)) (hpair : PairAt s.mem p A B)
    (hcov : Covers [pairR p, callR q] s.wr) :
    WP isa (Impl.Sha3.AArch64.Neon.X2.call sha3 rp rb off) s fun t =>
      CallKeep s t ∧ Frame [pairR p, callR q] s.mem t.mem ∧
        PairAt t.mem p (keccakF A) (keccakF B) := by
  have hsub : Covers [pairR p, scrR q] [pairR p, callR q] := Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨pairR p, by simp, 0, (BitVec.add_zero p).symm, Nat.le_of_eq (Nat.zero_add _)⟩
    · exact ⟨callR q, by simp, 0, (BitVec.add_zero q).symm, by simp only [scrR, callR]; decide⟩
  have hscr : Region.Sub (scrR q) (callR q) := Region.sub_prefix (by decide : 128 ≤ 136)
  have hslotS : Region.Sub ⟨q + BitVec.ofNat 64 128, 8⟩ (callR q) :=
    Offset.sub_base q (d := 128) (n := 8) (k := 136) (by decide)
  have hpq' : (pairR p).Disjoint (scrR q) := hpq.sub_right hscr
  have hslot : InRegions s.wr (q + BitVec.ofNat 64 128) 8 :=
    hcov _ _ ⟨callR q, by simp, Offset.contains_base q (by decide) (by decide)⟩
  have hslotR : (callR q).Contains (q + BitVec.ofNat 64 128) 8 := Offset.contains_base q (by decide) (by decide)
  have hslot_sep : ∀ r ∈ [pairR p, scrR q], (⟨q + BitVec.ofNat 64 128, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hpq.sub_right hslotS).symm
    · exact Offset.disjoint_base q (d := 128) (n := 8) (k := 128) (by decide) (by decide)
  unfold Impl.Sha3.AArch64.Neon.X2.call
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_addImm (by omega) fun s₁ o₁ e₁ =>
    VG.Proof.MlKem.AArch64.wp_addImm (by omega) fun s₂ o₂ e₂ => ?_)
  have h1 : s₂.gpr .x1 = q := by
    rw [e₂, e₁, ← hq, BitVec.add_assoc, ← BitVec.ofNat_add,
      show off / 2 + (off - off / 2) = off by omega]
  refine wp_str ⟨by decide, by decide⟩ (by rw [h1]) (by rw [o₂.wr, o₁.wr]; exact hslot)
    fun s₃ m₃ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₄ o₄ e₄ => WP.block_nil ?_
  have h0 : s₄.gpr .x0 = p := by
    rw [e₄, BitVec.add_zero, m₃.gpr, o₂.gpr _ (by simpa using hrp), o₁.gpr _ (by simpa using hrp), hp]
  have h1' : s₄.gpr .x1 = q := by rw [o₄.gpr _ (by decide), m₃.gpr, h1]
  have hlr : ∀ r, r ≠ .x0 → r ≠ .x1 → s₄.gpr r = s.gpr r := fun r h0 h1 => by
    rw [o₄.gpr _ (by simpa using h0), m₃.gpr, o₂.gpr _ (by simpa using h1), o₁.gpr _ (by simpa using h1)]
  have hm : s₄.mem = s.mem.writeW (q + BitVec.ofNat 64 128) (s.gpr .x30) := by
    rw [o₄.mem, m₃.mem, o₂.mem, o₁.mem, o₂.gpr _ (by decide), o₁.gpr _ (by decide)]
  have hw : s₄.wr = s.wr := o₄.wr.trans (m₃.wr.trans (o₂.wr.trans o₁.wr))
  refine WP.seq (WP.callV (k := K) (rd := []) (wr := [pairR p, scrR q]) (correct sha3)
    ⟨rfl, by simp only [State.withRegions_wr, State.withRegions_gpr,
        State.callEntry_gpr s₄ (show Reg.x0 ∉ linkRegs by decide),
        State.callEntry_gpr s₄ (show Reg.x1 ∉ linkRegs by decide), h0, h1'],
      by simpa only [State.withRegions_gpr,
        State.callEntry_gpr s₄ (show Reg.x0 ∉ linkRegs by decide),
        State.callEntry_gpr s₄ (show Reg.x1 ∉ linkRegs by decide), h0, h1'] using hpq'⟩
    (by rw [hw]; exact Covers.right (hsub.trans hcov)) (by rw [hw]; exact hsub.trans hcov) ?_
    (code_noFrames sha3))
  intro t hr hwr hsp hf _ hk _ hpost
  have hkt : ∀ r, r ≠ .x16 → r ∉ linkRegs → t.gpr r = s₄.gpr r := fun r h16 hl =>
    hk r hl (code_writes sha3 r h16)
  have ht1 : t.gpr .x1 = q := (hkt .x1 (by decide) (by decide)).trans h1'
  have hf₄ : Frame [callR q] s.mem s₄.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hslotR
  have hpair₄ : PairAt s₄.mem p A B := fun i hi => by
    rw [hf₄.read (pair_contains p hi) (by simpa using hpq) (by decide)]; exact hpair i hi
  simp only [K, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    State.callEntry_gpr s₄ (show Reg.x0 ∉ linkRegs by decide), h0] at hpost
  obtain ⟨hA, hB⟩ := stateX2_of_pairAt hpair₄
  rw [hA, hB] at hpost
  have hval : t.mem.readW (q + BitVec.ofNat 64 128) 64 = s.gpr .x30 := by
    rw [hf.readW (r := ⟨q + BitVec.ofNat 64 128, 8⟩) (Region.contains_self _ _) hslot_sep (by decide),
      hm, Mem.readW_writeW_self64]
  refine VG.Proof.Sha3.AArch64.wp_ldr ⟨by decide, by decide⟩ (by rw [ht1])
    (by rw [hr, hwr, hw, o₄.rd, m₃.rd, o₂.rd, o₁.rd]
        obtain ⟨R, hR, hc⟩ := hslot
        exact ⟨R, List.mem_append_right _ hR, hc⟩)
    fun u hu => WP.block_nil ⟨⟨fun r hr' => ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    by_cases h30 : r = .x30
    · subst r; rw [hu.gpr, hval]
    · rw [hu.other r h30, hkt r hr'.2.2.1 (by simp [linkRegs, h30, hr'.2.2.1, hr'.2.2.2]),
        hlr r hr'.1 hr'.2.1]
  · rw [hu.rd, hr, o₄.rd, m₃.rd, o₂.rd, o₁.rd]
  · rw [hu.wr, hwr, hw]
  · rw [hu.sp, hsp, o₄.sp, m₃.sp, o₂.sp, o₁.sp]
  · rw [hu.mem]
    refine (hf₄.mono (fun r hr => by simp at hr; simp [hr])).trans (hf.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨pairR p, by simp, fun _ h => h⟩
    · exact ⟨callR q, by simp, hscr⟩
  · rw [hu.mem]
    have := pairAt_stateX2 t.mem p
    rwa [hpost.1, hpost.2] at this

/-! ## The squeeze -/

/-- The first `n` words of each state, `ldr` from the pair and `str` to `a` and `b`. -/
def outN (a : Addr) (n : Nat) : Region := ⟨a, 8 * n⟩

theorem word0 {m : Mem} {p : Addr} {A B : Spec.Sha3.State} (h : PairAt m p A B) {i : Nat} (hi : i < 25) :
    m.readW (p + BitVec.ofNat 64 (16 * i)) 64 = A[i]! := by
  have := congrArg (vdword · 0) (h i hi)
  simp only [vdword_read16 _ _ (show 0 < 2 by decide), vdword_ofVDwords_0, wordAddr,
    Nat.mul_zero, BitVec.add_zero] at this
  exact this

theorem word1 {m : Mem} {p : Addr} {A B : Spec.Sha3.State} (h : PairAt m p A B) {i : Nat} (hi : i < 25) :
    m.readW (p + BitVec.ofNat 64 (16 * i + 8)) 64 = B[i]! := by
  have := congrArg (vdword · 1) (h i hi)
  simp only [vdword_read16 _ _ (show 1 < 2 by decide), vdword_ofVDwords_1, wordAddr] at this
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at this
  exact this

theorem out_contains (a : Addr) {n i : Nat} (hi : i < n) (hn : n ≤ 25) :
    (outN a n).Contains (outAddr a i) 8 := Offset.contains_base a (by omega) (by omega)

theorem contains_halves {r : Region} {a : Addr} (h : r.Contains a 16) :
    r.Contains a 8 ∧ r.Contains (a + BitVec.ofNat 64 8) 8 := by
  unfold Region.Contains at *
  have e : a + BitVec.ofNat 64 8 - r.base = (a - r.base) + BitVec.ofNat 64 8 := by
    simp only [BitVec.sub_eq_add_neg]; ac_rfl
  have hm := Nat.mod_le ((a - r.base).toNat + (BitVec.ofNat 64 8).toNat) (2 ^ 64)
  rw [e, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat] at hm ⊢
  omega

theorem squeeze_step {s : State} {p a b : Addr} {rp ra rb : Reg} {i : Nat} (hi : i < 25)
    (hp : s.gpr rp = p) (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (hp6 : rp ≠ .x6) (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hin : InRegions (s.rd ++ s.wr) (wordAddr p i) 16)
    (hwa : InRegions s.wr (outAddr a i) 8) (hwb : InRegions s.wr (outAddr b i) 8) :
    WP isa (.block ([.ldr .x .x6 rp (16*i), .ldr .x .x7 rp (16*i+8),
      .str .x .x6 ra (8*i), .str .x .x7 rb (8*i)] : List Instr)) s fun t =>
      OutKeep s t ∧ t.mem = (s.mem.writeW (outAddr a i) (s.mem.readW (p + BitVec.ofNat 64 (16*i)) 64)).writeW
        (outAddr b i) (s.mem.readW (p + BitVec.ofNat 64 (16*i+8)) 64) := by
  obtain ⟨R, hR, hc⟩ := hin
  have hin0 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16*i)) 8 :=
    ⟨R, hR, (contains_halves hc).1⟩
  have hin1 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16*i+8)) 8 := by
    refine ⟨R, hR, ?_⟩
    have := (contains_halves hc).2
    rwa [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add] at this
  refine wp_ldr ⟨by omega, by omega⟩ (by rw [hp]) hin0 fun s₁ h₁ => ?_
  refine wp_ldr ⟨by omega, by omega⟩ (by rw [h₁.other rp hp6, hp])
    (by rw [h₁.rd, h₁.wr]; exact hin1) fun s₂ h₂ => ?_
  refine wp_str ⟨by omega, by omega⟩ (by rw [h₂.other ra ha7, h₁.other ra ha6, ha])
    (by rw [h₂.wr, h₁.wr]; exact hwa) fun s₃ h₃ => ?_
  refine wp_str ⟨by omega, by omega⟩ (by rw [h₃.gpr, h₂.other rb hb7, h₁.other rb hb6, hb])
    (by rw [h₃.wr, h₂.wr, h₁.wr]; exact hwb) fun s₄ h₄ => WP.block_nil_iff.mpr ⟨?_, ?_⟩
  · exact ((OutKeep.upd h₁ (Or.inl rfl)).trans (OutKeep.upd h₂ (Or.inr rfl))).trans
      ((OutKeep.mem h₃).trans (OutKeep.mem h₄))
  · rw [h₄.mem, h₃.mem, h₃.gpr, h₂.gpr, h₂.other .x6 (by decide), h₁.gpr, h₂.mem, h₁.mem]
    rfl

/-- The first `n` words of both states, from the pair at `p` to `a` and `b`. -/
theorem squeeze_ok {n : Nat} (hn : n ≤ 25) {s : State} {p a b : Addr} {rp ra rb : Reg}
    {A B : Spec.Sha3.State}
    (hp : s.gpr rp = p) (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (hp6 : rp ≠ .x6) (hp7 : rp ≠ .x7) (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hpair : PairAt s.mem p A B) (hd : (outN a n).Disjoint (outN b n))
    (hpa : (pairR p).Disjoint (outN a n)) (hpb : (pairR p).Disjoint (outN b n))
    (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (wordAddr p i) 16)
    (hwa : ∀ i < n, InRegions s.wr (outAddr a i) 8)
    (hwb : ∀ i < n, InRegions s.wr (outAddr b i) 8) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.X2.squeeze n rp ra rb)) s fun t =>
      OutKeep s t ∧ Frame [outN a n, outN b n] s.mem t.mem ∧
      (∀ i < n, t.mem.readW (outAddr a i) 64 = A[i]!) ∧
      (∀ i < n, t.mem.readW (outAddr b i) 64 = B[i]!) := by
  unfold Impl.Sha3.AArch64.Neon.X2.squeeze
  refine wp_range_flatMap (M := isa)
    (fun k t => OutKeep s t ∧ Frame [outN a n, outN b n] s.mem t.mem ∧
      (∀ i < k, t.mem.readW (outAddr a i) 64 = A[i]!) ∧
      (∀ i < k, t.mem.readW (outAddr b i) 64 = B[i]!))
    (fun k t hk ⟨ht, hf, hva, hvb⟩ => ?_) n (Nat.le_refl _) s
    ⟨OutKeep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hpt : PairAt t.mem p A B := fun i hi => by
    rw [hf.read (pair_contains p hi) (by simp [hpa, hpb]) (by decide)]; exact hpair i hi
  refine WP.mono (squeeze_step (by omega) ((ht.gpr rp hp6 hp7).trans hp)
    ((ht.gpr ra ha6 ha7).trans ha) ((ht.gpr rb hb6 hb7).trans hb) hp6 ha6 ha7 hb6 hb7
    (by rw [ht.rd, ht.wr]; exact hin k (by omega))
    (by rw [ht.wr]; exact hwa k hk) (by rw [ht.wr]; exact hwb k hk))
    fun u ⟨hu, hm⟩ => ⟨ht.trans hu, ?_, ?_, ?_⟩
  · rw [hm]
    exact (hf.writeW (by simp) _ (out_contains a hk hn)).writeW (by simp) _ (out_contains b hk hn)
  · intro i hi
    rw [hm, Mem.readW_writeW_sep (hd.sep (out_contains a (by omega) hn) (out_contains b hk hn))
      (by decide)]
    by_cases he : i = k
    · subst i
      rw [Mem.readW_writeW_self64, word0 hpt (by omega)]
    · rw [Mem.readW_writeW_sep (Offset.sep a (d := 8*i) (n := 8) (e := 8*k) (k := 8)
        (by omega) (by omega) (by omega)) (by decide)]
      exact hva i (by omega)
  · intro i hi
    rw [hm]
    by_cases he : i = k
    · subst i
      rw [Mem.readW_writeW_self64, word1 hpt (by omega)]
    · rw [Mem.readW_writeW_sep (Offset.sep b (d := 8*i) (n := 8) (e := 8*k) (k := 8)
        (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (hd.symm.sep (out_contains b (by omega) hn) (out_contains a hk hn))
          (by decide)]
      exact hvb i (by omega)

end VG.Proof.Sha3.AArch64.Neon.X2
