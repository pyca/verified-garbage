import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMr

/-!
# A candidate on x86-64: constant time of one bit of Miller–Rabin

`mrExpBit` in four pieces: the squaring, the selection of the factor, the
multiplication, the comparisons and the flag. Between them, what each run
keeps (`BitW`): the header, and enough of the arithmetic for the
multiplications to run (`MrCtx`, `y < c`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The public data of a bit: Miller–Rabin's, the witnesses so far, the
octets read, the words left and the bits left of the word. -/
structure BPub where
  p : MrPub
  i : Nat
  u : Nat
  k : Nat
  n : Nat

/-- The header words public during a bit. -/
abbrev BPub.vs (q : BPub) : List (Nat × BitVec 64) :=
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

theorem BPub.vs_lt (q : BPub) : ∀ e ∈ q.vs, e.1 < 32 :=
  q.p.vs_lt q.i q.u _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; decide)

/-- What each run keeps between the pieces of a bit. -/
def BitW (q : BPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr q.vs s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (c b : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c (b * 2 ^ (64 * q.p.w) % c) ∧ c % 2 = 1 ∧
      1 < c ∧ wv s.mem q.p.B (slot q.p.w aY) q.p.w < c

theorem BitW.goodW {q : BPub} {s : State} (h : BitW q s) : GoodW ⟨q.p.B, q.p.Z, q.p.w⟩ s :=
  let ⟨_, _, hd, mi, _, _, hc, _⟩ := h; ⟨mi, hc.good, hd.z⟩

/-- `BitW` after a multiplication `o := a b`, `o` one of the working arrays. -/
theorem bitW_mm (M : Mont) {q : BPub} {s : State} (h : BitW q s) {o a b : Nat} (ho : o = aY ∨ o = aXm)
    (ha : a < 8) (hb : b < 8) (d3 : a ≠ aAcc) (d4 : b ≠ aAcc) (d5 : a ≠ aTmp) (d6 : b ≠ aTmp)
    (hB : wv s.mem q.p.B (slot q.p.w b) q.p.w < wv s.mem q.p.B (slot q.p.w aN) q.p.w) :
    WP isa (M.mm o a b) s fun t => BitW q t := by
  obtain ⟨hk, hp, hd, mi, c, bm, hc, hodd, hc1, hy⟩ := h
  have hw' : q.p.w < 2 ^ 31 := by have := hd.w64; omega
  have ho8 : o < 8 := by rcases ho with rfl | rfl <;> decide
  have d1 : o ≠ aAcc := by rcases ho with rfl | rfl <;> decide
  have d2 : o ≠ aTmp := by rcases ho with rfl | rfl <;> decide
  refine WP.mono (M.mm_ok hc.good hd.z (by have := hd.w4; omega) hw' ho8 ha hb d1 d2 d3 d4 hc.inv hB d5 d6)
    fun t ⟨hg, hlt, _, ha', k⟩ => ?_
  have hrs : ∀ j ∈ [aAcc, aTmp, o], (slot q.p.w j, 8 * (q.p.w + 2)) ∈ [(slot q.p.w aAcc, 8 * (q.p.w + 2)),
      (slot q.p.w aTmp, 8 * (q.p.w + 2)), (slot q.p.w o, 8 * (q.p.w + 2))] := by simp
  have hf := Frm.of_arrays ha' hrs
  have hc' : MrCtx t q.p.B q.p.Z q.p.w mi c (bm * 2 ^ (64 * q.p.w) % c) := by
    refine hc.of_frm hd hf hg.scr hg.rdi ?_ ?_ ?_ ?_ ?_ <;> rcases ho with rfl | rfl <;> rng_disj
  refine ⟨hk, hp.frm hf (by rcases ho with rfl | rfl <;> rng_le) q.vs_lt hg.rdi k.2.2, hd, mi, c, bm, hc', hodd, hc1, ?_⟩
  rcases ho with rfl | rfl
  · rw [← hc.n]; exact hlt
  · rw [hf.wv_eq (d := slot q.p.w aY) (k := q.p.w) (by rng_disj)
      (by have := hc.good.scr.nowrap; have := slot_le (w := q.p.w) (show aY < 8 by decide); have := hd.z; omega)]
    exact hy

theorem shr63_bool (V : BitVec 64) : ∃ bt : Bool, V >>> 63 = BitVec.ofNat 64 bt.toNat := by
  have h : (V >>> 63).toNat = V.toNat / 2 ^ 63 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := V.isLt
  by_cases hb : V.toNat / 2 ^ 63 = 1
  · exact ⟨true, BitVec.eq_of_toNat_eq (by rw [h, hb]; rfl)⟩
  · exact ⟨false, BitVec.eq_of_toNat_eq (by rw [h]; show _ = 0; omega)⟩

/-- The selection keeps `BitW`, with a factor below `c`. -/
theorem bitW_sel {q : BPub} {s : State} (h : BitW q s) :
    WP isa (.seq (.block (([.mov .rax (.mem (hdr kV)), .shift .shr .rax 63, .mov32 .r15 (.imm 0),
        .alu .sub .r15 (.reg .rax), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aXm)))] : List Instr) ++
        extBase aB .r8 ++ extBase aR1 .rsi))
      (wordLoop 0 [.mov .rax (.mem (ix .r8 .r14)), .mov .rdx (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .rdx),
        .alu .and .rax (.reg .r15), .alu .xor .rax (.reg .rdx), .store (ix .rbx .r14) .rax])) s fun t =>
      BitW q t ∧ wv t.mem q.p.B (slot q.p.w aXm) q.p.w < wv t.mem q.p.B (slot q.p.w aN) q.p.w := by
  obtain ⟨hk, hp, hd, mi, c, bm, hc, hodd, hc1, hy⟩ := h
  have hg := hc.good
  have hZ := hd.z
  have hXZ := hd.x
  have hw' : q.p.w < 2 ^ 31 := by have := hd.w64; omega
  have hn := hg.scr.nowrap
  obtain ⟨bt, hbt⟩ := shr63_bool (word s.mem q.p.B (8 * kV))
  refine WP.seq (WP.mono (bitSel_ok hg hZ hw' rfl hbt) fun s₂ ⟨h15, h12, hbx, h8, hsi, hm₂, k₂⟩ => ?_)
  have hs₂ := hg.scr.congr k₂.2.2
  refine WP.mono (selLoop_ok hs₂ h8 hsi hbx h15 h12 (by have := hd.w4; omega) hw'
    (by unfold slot aB aRm1 at *; omega) (by unfold slot aR1 aRm1 at *; omega)
    (by have := slot_le (w := q.p.w) (show aXm < 8 by decide); omega)
    (Or.inl (by unfold slot aXm aB; omega)) (Or.inl (by unfold slot aXm aR1; omega)))
    fun t ⟨hv, hst, ho, k⟩ => ?_
  have hdi : t.gpr .rdi = q.p.B := (k.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hg.rdi)
  have hf : Frm q.p.B [(slot q.p.w aXm, 8 * (q.p.w + 2))] s.mem t.mem := by
    rw [← hm₂]; exact Frm.of_outside (ho.mono (o' := slot q.p.w aXm) (n' := 8 * (q.p.w + 2)) (Nat.le_refl _) (by omega))
      (by simp)
  have hgt : Good t q.p.B q.p.Z q.p.w mi := ⟨hst, hdi, Hdr.of_frm hg.hdr hf (by rng_le)⟩
  have hc' := hc.of_frm hd hf hst hdi (by rng_le) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj)
  refine ⟨⟨hk, hp.frm hf (by rng_le) q.vs_lt hdi (k.2.2.trans k₂.2.2), hd, mi, c, bm, hc', hodd, hc1, ?_⟩, ?_⟩
  · rw [hf.wv_eq (d := slot q.p.w aY) (k := q.p.w) (by rng_disj)
      (by have := slot_le (w := q.p.w) (show aY < 8 by decide); omega)]
    exact hy
  · have hc0 : 0 < c := by omega
    rw [hv, hm₂, hc'.n, ← hf.wv_eq (d := slot q.p.w aB) (k := q.p.w) (by rng_disj) (by unfold slot aB aRm1 at *; omega),
      ← hf.wv_eq (d := slot q.p.w aR1) (k := q.p.w) (by rng_disj) (by unfold slot aR1 aRm1 at *; omega), hc'.b, hc'.r1]
    cases bt
    · exact Nat.mod_lt _ hc0
    · exact Nat.mod_lt _ hc0

theorem BPub.vs_fst (q : BPub) : q.vs.map (·.1) = mrS ++ [kWords, kBits] := q.p.vs_fst q.i q.u _

/-- A bit of the exponentiation leaks the same in runs that agree on the
public data. -/
theorem mrExpBit_ct (M : Mont) : RelCT isa (Two BitW) (seqs (mrExpBit M.mm)) fun _ _ => True := by
  rw [mrExpBit_eq]
  refine RelCT.seqs_app (by simp) (by simp [eqMask]) (RelCT.seq (R := Two BitW) ?_ ?_)
  · simp only [seqs]
    refine RelCT.seq (two_post (Ψ := BitW) (two_map (fun q : BPub => (⟨q.p.B, q.p.Z, q.p.w⟩ : Ws))
      (fun _ _ h => h.goodW) (M.ct (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) fun q s h => bitW_mm M h (Or.inl rfl)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
          obtain ⟨_, _, hd, mi, c, bm, hc, _, _, hy⟩ := h; rw [hc.n]; exact hy)) (RelCT.assoc (RelCT.seq (R := Two fun q s => BitW q s ∧
        wv s.mem q.p.B (slot q.p.w aXm) q.p.w < wv s.mem q.p.B (slot q.p.w aN) q.p.w) ?_ ?_))
    · exact kt_piece (fun q : BPub => q.p.B) (fun q => q.p.wr) (mrS ++ [kWords, kBits]) BPub.vs [] (by decide)
        BPub.vs_fst (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) fun _ _ h => bitW_sel h
    · exact two_post (two_map (fun q : BPub => (⟨q.p.B, q.p.Z, q.p.w⟩ : Ws)) (fun _ _ h => h.1.goodW)
        (M.ct (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))) fun q s h => bitW_mm M h.1 (Or.inl rfl)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.2
  · exact kt_ct (fun q : BPub => q.p.B) (fun q => q.p.wr) (mrS ++ [kWords, kBits]) BPub.vs [] (by decide)
      BPub.vs_fst (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide)

end VG.Proof.RsaKeyGen.X86_64
