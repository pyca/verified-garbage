import VerifiedGarbage.Proof.Weierstrass.X86.LadderPCall
import VerifiedGarbage.Proof.Weierstrass.X86.Ladder

/-!
# The ladder by calls of the point functions, on x86 (32-bit)

`ladderP L S ao` (`Impl/Weierstrass/X86/LadderP.lean`) meets what
`ladder_ok` states of `ladder L S` (`ladderP_ok`), but that it also writes
the point functions' slots and own working space (`ptW`, empty for P-521,
whose ladder is `ladder`), as on 32-bit ARM
(`Proof/Weierstrass/Arm/LadderP.lean`). Its calls use 28 bytes of stack
below `esp`, apart from the working space, and load `edi` again from the
caller's argument at `[esp + ao]`, which they leave alone (`LadArg`).
-/

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass.X86.Point
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
  VG.Proof.Weierstrass.X86.Mont

/-- The point functions' slots and own working space, which the ladder
writes if it calls them. -/
def ptW (n : Nat) : List (Nat × Nat) :=
  if 3 ≤ n ∧ n ≤ 6 then [(Spec.Weierstrass.Point.oAt n, 4096 - Spec.Weierstrass.Point.oAt n)] else []

/-- What `ladderP` writes. -/
def ladWp (L : LadderCfg) (wk : Nat) : List (Nat × Nat) := ladWx L wk ++ ptW L.M.n

/-- The ladder's slots and modulus lie below the point functions' slots. -/
structure LadPt (L : LadderCfg) : Prop where
  k3 : 3 ≤ L.M.n
  sl : ∀ x ∈ ladSlots L, x + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n
  mo : L.M.mo + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n

theorem MulOk.odd {n m : Nat} (h : MulOk n m) : m % 2 = 1 := by
  have h2 : (m * minv m + 1) % 2 = 0 := by
    rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide), h.inv]
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
  · simp [Nat.add_mod, Nat.mul_mod, h0] at h2
  · exact h1

section enc
variable (k : Nat) (dbl : Bool)

theorem enc_0 : enc k dbl 0 = Spec.Weierstrass.Point.oAt k := by simp [enc]
theorem enc_1 : enc k dbl 1 = Spec.Weierstrass.Point.oAt k + Spec.Weierstrass.Point.elemBytes k := by simp [enc]
theorem enc_2 : enc k dbl 2 = Spec.Weierstrass.Point.oAt k + 2 * Spec.Weierstrass.Point.elemBytes k := by simp [enc]; omega
theorem enc_3 : enc k dbl 3 = Spec.Weierstrass.Point.pAt k := by simp [enc]
theorem enc_4 : enc k dbl 4 = Spec.Weierstrass.Point.pAt k + Spec.Weierstrass.Point.elemBytes k := by simp [enc]
theorem enc_5 : enc k dbl 5 = Spec.Weierstrass.Point.pAt k + 2 * Spec.Weierstrass.Point.elemBytes k := by simp [enc]; omega
theorem enc_6 : enc k dbl 6 = if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k := by simp [enc]
theorem enc_7 : enc k dbl 7 = (if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k) + Spec.Weierstrass.Point.elemBytes k := by
  simp [enc]
theorem enc_8 : enc k dbl 8 = (if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k) + 2 * Spec.Weierstrass.Point.elemBytes k := by
  simp [enc]; omega
theorem enc_9 : enc k dbl 9 = Spec.Weierstrass.Point.aAt k := by simp [enc]
theorem enc_10 : enc k dbl 10 = Spec.Weierstrass.Point.b3At k := by simp [enc]

end enc

/-- The bounds a call needs, by offset. -/
theorem rIds_lt_of {k m : Nat} (dbl : Bool) {mem : Mem} {base : Addr}
    (h : ∀ x ∈ [Spec.Weierstrass.Point.pAt k, Spec.Weierstrass.Point.pAt k + Spec.Weierstrass.Point.elemBytes k, Spec.Weierstrass.Point.pAt k + 2 * Spec.Weierstrass.Point.elemBytes k,
      (if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k), (if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k) + Spec.Weierstrass.Point.elemBytes k,
      (if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k) + 2 * Spec.Weierstrass.Point.elemBytes k, Spec.Weierstrass.Point.aAt k, Spec.Weierstrass.Point.b3At k],
      wordsVal mem base x k < m) :
    ∀ x ∈ rIds, wordsVal mem base (enc k dbl x) k < m := by
  intro x hx
  simp only [rIds, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10] <;> exact h _ (by simp)

/-- The point functions' `Q`, `a` and `3b` in `m` hold `G`, `a` and `3b` of
`m₀`. -/
def CpOk (L : LadderCfg) (base : Addr) (m m₀ : Mem) : Prop :=
  wordsVal m base (Spec.Weierstrass.Point.qAt L.M.n) L.M.n = wordsVal m₀ base L.G.x L.M.n ∧
  wordsVal m base (Spec.Weierstrass.Point.qAt L.M.n + Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n =
    wordsVal m₀ base L.G.y L.M.n ∧
  wordsVal m base (Spec.Weierstrass.Point.qAt L.M.n + 2 * Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n =
    wordsVal m₀ base L.G.z L.M.n ∧
  wordsVal m base (Spec.Weierstrass.Point.aAt L.M.n) L.M.n = wordsVal m₀ base L.S.a L.M.n ∧
  wordsVal m base (Spec.Weierstrass.Point.b3At L.M.n) L.M.n = wordsVal m₀ base L.S.b3 L.M.n

/-- The copies survive changes apart from them. -/
theorem CpOk.keep {L : LadderCfg} {base : Addr} {m m' m₀ : Mem} (h : CpOk L base m m₀)
    (hk3 : 3 ≤ L.M.n) (hk6 : L.M.n ≤ 6) {W : List (Nat × Nat)} (hU : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ Spec.Weierstrass.Point.qAt L.M.n ∨ Spec.Weierstrass.Point.ownAt L.M.n ≤ w.1) :
    CpOk L base m' m₀ := by
  have hl := lay_nums hk3 hk6
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hU.wordsVal (fun w hw => by have := hW w hw; omega) (by omega)]; exact h1
  · rw [hU.wordsVal (fun w hw => by have := hW w hw; omega) (by omega)]; exact h2
  · rw [hU.wordsVal (fun w hw => by have := hW w hw; omega) (by omega)]; exact h3
  · rw [hU.wordsVal (fun w hw => by have := hW w hw; omega) (by omega)]; exact h4
  · rw [hU.wordsVal (fun w hw => by have := hW w hw; omega) (by omega)]; exact h5

/-- The caller's argument at `[esp + ao]` holding `edi`, readable, apart
from the working space and from the 28 bytes of stack below `esp`, which
are apart from the working space too. -/
structure LadArg (s : State) (base : Addr) (ao : Nat) : Prop where
  s28 : 28 ≤ (s.gpr .esp).toNat
  sz : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + 8192 + 28 ≤ (s.gpr .esp).toNat
  rd : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) ao) 4
  val : s.mem.readW (addr (s.gpr .esp) ao) 32 = s.gpr .edi
  aw : Region.Disjoint ⟨addr (s.gpr .esp) ao, 4⟩ ⟨base, 8192⟩
  as : Region.Disjoint ⟨addr (s.gpr .esp) ao, 4⟩ (below (s.gpr .esp) 28)

/-- The argument survives a change of the registers but `esp` and `edi`, and
of memory within the working space and the stack below `esp`. -/
theorem LadArg.keep {s s' : State} {base : Addr} {ao : Nat} (h : LadArg s base ao)
    (hsp : s'.gpr .esp = s.gpr .esp) (hedi : s'.gpr .edi = s.gpr .edi) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame [⟨base, 8192⟩, below (s.gpr .esp) 28] s.mem s'.mem) :
    LadArg s' base ao := by
  refine ⟨by rw [hsp]; exact h.s28, by rw [hsp]; exact h.sz, by rw [hsp, hrd, hwr]; exact h.rd, ?_,
    by rw [hsp]; exact h.aw, by rw [hsp]; exact h.as⟩
  rw [hsp, hedi, hf.readW (r := ⟨addr (s.gpr .esp) ao, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.aw
    · exact h.as) (by decide), h.val]

/-- The `z` bytes below `sp` (`z ≥ 28`) apart from the working space. -/
theorem sep_of {sp : BitVec 32} {base : Addr} {z : Nat} (hz : 28 ≤ z)
    (hn : base.toNat + 8192 ≤ 2 ^ 32)
    (hd : Region.Disjoint ⟨sp.setWidth 64 - BitVec.ofNat 64 z, z⟩ ⟨base, 8192⟩) :
    sp.toNat ≤ base.toNat ∨ base.toNat + 8192 + 28 ≤ sp.toNat := by
  by_contra h
  simp only [not_or, Nat.not_le] at h
  have hb := sp.isLt
  by_cases hc : base.toNat + z ≤ sp.toNat
  · refine hd (sp.setWidth 64 - BitVec.ofNat 64 z) ?_ ?_
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    · simp only [Region.Contains]
      bv_omega
  · refine hd base ?_ ?_
    · simp only [Region.Contains]
      bv_omega
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- The argument at `[esp + ao]`, from a caller's `z ≥ 28` bytes of stack
apart from the working space. -/
theorem LadArg.of {s : State} {base : Addr} {ao z : Nat} (hz : 28 ≤ z) (hsp : z ≤ (s.gpr .esp).toNat)
    (hfit : (s.gpr .esp).toNat + ao + 4 ≤ 2 ^ 32) (hn : base.toNat + 8192 ≤ 2 ^ 32)
    (hd : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 z, z⟩ ⟨base, 8192⟩)
    (hrd : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) ao) 4)
    (hval : s.mem.readW (addr (s.gpr .esp) ao) 32 = s.gpr .edi)
    (haw : Region.Disjoint ⟨addr (s.gpr .esp) ao, 4⟩ ⟨base, 8192⟩) : LadArg s base ao := by
  have ha : (addr (s.gpr .esp) ao).toNat = (s.gpr .esp).toNat + ao := by
    simp only [addr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨by omega, sep_of hz hn hd, hrd, hval, haw, Region.disjoint_of_le (.inr (by
    show (below (s.gpr .esp) 28).base.toNat + 28 ≤ (addr (s.gpr .esp) ao).toNat
    rw [below_toNat _ (by omega), ha]; omega)) (by show _ + 4 ≤ _; rw [ha]; omega)
    (by show (below (s.gpr .esp) 28).base.toNat + 28 ≤ _; rw [below_toNat _ (by omega)]; omega)⟩

/-- Ranges of offsets of the working space are apart from what is outside it. -/
theorem frame_of_outs {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ 8192) :
    Frame [⟨base, 8192⟩] m m' := fun x hx => h x fun r hr => .inr (by
  have h1 : ¬ ((⟨base, 8192⟩ : Region).Contains x 1) := hx _ (List.mem_singleton_self _)
  have := hrs r hr
  simp only [Region.Contains, ofs] at h1 ⊢
  omega)

/-- The loop's invariant at `esi = j`: `Q j` accepts what `R` holds, the
point functions' `Q`, `a` and `3b` hold `G`, `a` and `3b`, and the caller's
argument still holds `edi`. -/
structure LadInvP (L : LadderCfg) (wk : Nat) (C : Spec.Weierstrass.Curve) (base : Addr) (size ao : Nat)
    (Q : Nat → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Prop)
    (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  esi : s.gpr .esi = BitVec.ofNat 32 j
  keep : Keeps powClob s₀ s
  unch : Unch base (ladWx L wk ++ [(Spec.Weierstrass.Point.oAt L.M.n, 4096 - Spec.Weierstrass.Point.oAt L.M.n)])
    s₀.mem s.mem
  mod : ModOkW L.M size C.p s.mem base
  lt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s.mem base x L.M.n < C.p
  q : Q j (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)
  cp : CpOk L base s.mem s₀.mem
  arg : LadArg s base ao

/-- Apart from each of a few ranges, for numbers of the layout. -/
macro "apart_ranges" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq_or_imp, forall_eq, List.mem_singleton]; omega))

/-- As `apart_ranges`, among which memory past the working space. -/
macro "apart_rangesW" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq_or_imp, forall_eq, List.mem_singleton, VG.Proof.Weierstrass.X86.Mont.outW]; omega))

/-- Within the point functions' slots and own working space. -/
macro "in_pt" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq_or_imp, forall_eq, List.mem_singleton, exists_eq_left]; omega))


section body
variable {L : LadderCfg} {F : Spec.Weierstrass.Mont.Modulus} {wk : Nat} {C : Spec.Weierstrass.Curve}
  {base : Addr} {size ao : Nat}

/-- Each range a field program or a call writes lies within the point
functions' slots or past the working space. -/
theorem cover_pt {W : List (Nat × Nat)} {n : Nat}
    (h : ∀ w ∈ W, w = VG.Proof.Weierstrass.X86.Mont.outW ∨
      (Spec.Weierstrass.Point.oAt n ≤ w.1 ∧ w.1 + w.2 ≤ 4096)) {L' : List (Nat × Nat)}
    (ho : VG.Proof.Weierstrass.X86.Mont.outW ∈ L') :
    ∀ w ∈ W, ∃ w' ∈ L' ++ [(Spec.Weierstrass.Point.oAt n, 4096 - Spec.Weierstrass.Point.oAt n)],
      w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := fun w hw => by
  rcases h w hw with rfl | ⟨h1, h2⟩
  · exact ⟨_, List.mem_append_left _ ho, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), h1, by dsimp only; omega⟩

/-- An iteration. -/
theorem ladderPBody_ok {k : Nat} {Q : Nat → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Prop}
    (hL : LadLay L size) (hW : LadWk L F C.p size wk) (hk6 : L.M.n ≤ 6) (hP : LadPt L)
    {s₀ : State} (hlt₀ : ∀ x ∈ ladRo L, wordsVal s₀.mem base x L.M.n < C.p)
    (hstep : Step L C base s₀ k Q)
    (hbits : ∀ t < L.nbits, s₀.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ L.nbits) (hI : LadInvP L wk C base size ao Q s₀ s j) :
    WP isa (ladderPBody L F ao) s fun s' =>
      LadInvP L wk C base size ao Q s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have hFn := hW.fn
  have hk : F.k = L.M.n := hW.k
  have hm : F.m = C.p := hW.fm
  have hM : MulOk L.M.n C.p := by have h := hFn.mul; rw [hk, hm] at h; exact h
  have hodd := MulOk.odd hM
  have hk3 := hP.k3
  have hl := lay_nums hk3 hk6
  have hsz : size = 8192 := hW.size
  have hwk : wk = own L.M.n := hW.own
  have hown : own L.M.n + 64 * L.M.n = 4096 := (saveAt_le (by omega) (by omega)).2
  have hbl : 4096 ≤ L.bits := by have := hW.bits; omega
  have hbt := hW.bits_top
  have hnb := hL.nbits
  have rx : L.R.x + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hP.sl _ (ladPts_slots L _ (by simp))
  have ry : L.R.y + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hP.sl _ (ladPts_slots L _ (by simp))
  have rz : L.R.z + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hP.sl _ (ladPts_slots L _ (by simp))
  have hcov : ∀ {W : List (Nat × Nat)}, (∀ w ∈ W, w = VG.Proof.Weierstrass.X86.Mont.outW ∨
      (Spec.Weierstrass.Point.oAt L.M.n ≤ w.1 ∧ w.1 + w.2 ≤ 4096)) → ∀ w ∈ W,
      ∃ w' ∈ ladWx L wk ++ [(Spec.Weierstrass.Point.oAt L.M.n, 4096 - Spec.Weierstrass.Point.oAt L.M.n)],
        w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := fun h =>
    cover_pt h (by simp [ladWx])
  -- `esi -= 1`.
  rw [ladderPBody]
  refine WP.seq (wp_decCounter hj hI.esi fun s₁ b₁ k₁ hm₁ => WP.block_nil ?_)
  have hs₁ := hI.scr.of_keeps k₁ (by decide)
  -- `P = R`.
  refine WP.seq (WP.mono (copyPt_ok hs₁ (n := L.M.n) (o := ptAt L.M.n (Spec.Weierstrass.Point.pAt L.M.n))
    (a := L.R) (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [ptAt]; omega)
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega))
    fun s₂ ⟨px₂, py₂, pz₂, k₂, O₂⟩ => ?_)
  simp only [ptAt] at px₂ py₂ pz₂ O₂
  rw [hm₁] at px₂ py₂ pz₂ O₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have K₂ : Keeps powClob s s₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have arg₂ : LadArg s₂ base ao := hI.arg.keep (K₂.1 _ (by decide)) (K₂.1 _ (by decide)) K₂.2.1 K₂.2.2
    ((frame_of_outs O₂ (by apart_ranges)).mono (by simp))
  have cp₂ : CpOk L base s₂.mem s₀.mem := hI.cp.keep hk3 hk6 (Outs.unch O₂) (by apart_ranges)
  obtain ⟨gx₂, gy₂, gz₂, ga₂, gb₂⟩ := cp₂
  have la : wordsVal s₀.mem base L.S.a L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lb : wordsVal s₀.mem base L.S.b3 L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lgx : wordsVal s₀.mem base L.G.x L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lgy : wordsVal s₀.mem base L.G.y L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lgz : wordsVal s₀.mem base L.G.z L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lrx : wordsVal s.mem base L.R.x L.M.n < C.p := hI.lt _ (by simp)
  have lry : wordsVal s.mem base L.R.y L.M.n < C.p := hI.lt _ (by simp)
  have lrz : wordsVal s.mem base L.R.z L.M.n < C.p := hI.lt _ (by simp)
  -- `O = P + P`.
  refine WP.seq (WP.mono (ptCall_ok hFn hm hk hodd hk3 hk6 true (hsz ▸ hs₂) arg₂.s28 arg₂.sz arg₂.rd arg₂.val
      arg₂.aw arg₂.as (rIds_lt_of true fun x hx => by
      simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [px₂]; exact lrx
      · rw [py₂]; exact lry
      · rw [pz₂]; exact lrz
      · rw [px₂]; exact lrx
      · rw [py₂]; exact lry
      · rw [pz₂]; exact lrz
      · rw [ga₂]; exact la
      · rw [gb₂]; exact lb)) fun s₃ ⟨k₃, O₃, F₃, L₃, E₃⟩ => ?_)
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10, ↓reduceIte] at E₃
  rw [ga₂, gb₂, px₂, py₂, pz₂] at E₃
  have l3x := L₃ 0 (by decide)
  have l3y := L₃ 1 (by decide)
  have l3z := L₃ 2 (by decide)
  rw [enc_0] at l3x
  rw [enc_1] at l3y
  rw [enc_2] at l3z
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have arg₃ : LadArg s₃ base ao := arg₂.keep (k₃.1 _ (by decide)) (k₃.1 _ (by decide)) k₃.2.1 k₃.2.2 F₃
  -- `P = O`.
  refine WP.seq (WP.mono (copyPt_ok hs₃ (n := L.M.n) (o := ptAt L.M.n (Spec.Weierstrass.Point.pAt L.M.n))
    (a := ptAt L.M.n (Spec.Weierstrass.Point.oAt L.M.n))
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [ptAt]; omega)
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega))
    fun s₄ ⟨px₄, py₄, pz₄, k₄, O₄⟩ => ?_)
  simp only [ptAt] at px₄ py₄ pz₄ O₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have arg₄ : LadArg s₄ base ao := arg₃.keep (k₄.1 _ (by decide)) (k₄.1 _ (by decide)) k₄.2.1 k₄.2.2
    ((frame_of_outs O₄ (by apart_ranges)).mono (by simp))
  have cp₄ : CpOk L base s₄.mem s₀.mem :=
    (CpOk.keep ⟨gx₂, gy₂, gz₂, ga₂, gb₂⟩ hk3 hk6 (Outs.unch O₃) (by apart_rangesW)).keep hk3 hk6 (Outs.unch O₄)
      (by apart_ranges)
  obtain ⟨gx₄, gy₄, gz₄, ga₄, gb₄⟩ := cp₄
  -- `O = P + Q`.
  refine WP.seq (WP.mono (ptCall_ok hFn hm hk hodd hk3 hk6 false (hsz ▸ hs₄) arg₄.s28 arg₄.sz arg₄.rd arg₄.val
      arg₄.aw arg₄.as (rIds_lt_of false fun x hx => by
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [px₄]; exact l3x
      · rw [py₄]; exact l3y
      · rw [pz₄]; exact l3z
      · rw [gx₄]; exact lgx
      · rw [gy₄]; exact lgy
      · rw [gz₄]; exact lgz
      · rw [ga₄]; exact la
      · rw [gb₄]; exact lb)) fun s₅ ⟨k₅, O₅, F₅, L₅, E₅⟩ => ?_)
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10,
    Bool.false_eq_true, ↓reduceIte] at E₅
  rw [ga₄, gb₄, px₄, py₄, pz₄, gx₄, gy₄, gz₄] at E₅
  have l5x := L₅ 0 (by decide)
  have l5y := L₅ 1 (by decide)
  have l5z := L₅ 2 (by decide)
  rw [enc_0] at l5x
  rw [enc_1] at l5y
  rw [enc_2] at l5z
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have arg₅ : LadArg s₅ base ao := arg₄.keep (k₅.1 _ (by decide)) (k₅.1 _ (by decide)) k₅.2.1 k₅.2.2 F₅
  -- `P` still holds `D`.
  have p5x : wordsVal s₅.mem base (Spec.Weierstrass.Point.pAt L.M.n) L.M.n =
      wordsVal s₃.mem base (Spec.Weierstrass.Point.oAt L.M.n) L.M.n := by
    rw [(Outs.unch O₅).wordsVal (by apart_rangesW) (by omega), px₄]
  have p5y : wordsVal s₅.mem base (Spec.Weierstrass.Point.pAt L.M.n + Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n =
      wordsVal s₃.mem base (Spec.Weierstrass.Point.oAt L.M.n + Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n := by
    rw [(Outs.unch O₅).wordsVal (by apart_rangesW) (by omega), py₄]
  have p5z : wordsVal s₅.mem base (Spec.Weierstrass.Point.pAt L.M.n + 2 * Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n =
      wordsVal s₃.mem base (Spec.Weierstrass.Point.oAt L.M.n + 2 * Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n := by
    rw [(Outs.unch O₅).wordsVal (by apart_rangesW) (by omega), pz₄]
  have cp₅ : CpOk L base s₅.mem s₀.mem :=
    CpOk.keep ⟨gx₄, gy₄, gz₄, ga₄, gb₄⟩ hk3 hk6 (Outs.unch O₅) (by apart_rangesW)
  -- What changed: the point functions' slots and memory past the working space.
  have U₁₅r := ((Outs.unch O₂).trans (Outs.unch O₃)).trans ((Outs.unch O₄).trans (Outs.unch O₅))
  have U₁₅ : Unch base (ladWx L wk ++ [(Spec.Weierstrass.Point.oAt L.M.n, 4096 - Spec.Weierstrass.Point.oAt L.M.n)])
      s.mem s₅.mem :=
    U₁₅r.cover (hcov (by
      intro w hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact .inl rfl | exact .inr ⟨by dsimp only; omega, by dsimp only; omega⟩))
  have hU₅ : Unch base (ladWx L wk ++ [(Spec.Weierstrass.Point.oAt L.M.n, 4096 - Spec.Weierstrass.Point.oAt L.M.n)])
      s₀.mem s₅.mem :=
    (hI.unch.trans U₁₅).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw <;> exact hw
  have hbyte : s₅.mem (off base (L.bits + (j - 1))) = if k.testBit (j - 1) then 1 else 0 := by
    rw [hU₅.byte (fun w hw => by
      simp only [ladWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (hw | rfl | rfl) | rfl
      · have := hL.bits_w w hw; omega
      · dsimp only; omega
      · show _ ≤ 8192 ∨ _; omega
      · dsimp only; omega) (by omega), hbits _ (by omega)]
  have K₅ : Keeps powClob s s₅ :=
    K₂.trans <| (k₃.mono (by decide)).trans <| (k₄.mono (by decide)).trans (k₅.mono (by decide))
  have esi₅ : s₅.gpr .esi = BitVec.ofNat 32 (j - 1) := by
    rw [k₅.1 _ (by decide), k₄.1 _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide), b₁]
  -- `R = O` or `P`.
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (bitMask_bool_ok hs₅ esi₅ (by omega) hbyte) fun s₆ ⟨c₆, k₆, hm₆⟩ => ?_)
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  obtain ⟨rxy, rxz, ryz⟩ := hL.rne
  have hap : ∀ x ∈ [L.R.x, L.R.y, L.R.z], ∀ y ∈ [L.R.x, L.R.y, L.R.z], x ≠ y →
      x + 8 * L.M.n ≤ y ∨ y + 8 * L.M.n ≤ x := fun x hx y hy hxy =>
    hL.lay.apart x y (ladPts_slots L x (by simp only [List.mem_cons] at hx ⊢; rcases hx with h | h | h | h <;> simp [h]))
      (ladPts_slots L y (by simp only [List.mem_cons] at hy ⊢; rcases hy with h | h | h | h <;> simp [h])) hxy
  refine WP.block_append (WP.mono (selPt_ok hs₆ _ c₆ (n := L.M.n) (o := L.R)
    (a := ptAt L.M.n (Spec.Weierstrass.Point.pAt L.M.n)) (b := ptAt L.M.n (Spec.Weierstrass.Point.oAt L.M.n))
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    ⟨hap L.R.x (by simp) L.R.y (by simp) rxy, hap L.R.x (by simp) L.R.z (by simp) rxz,
      hap L.R.y (by simp) L.R.z (by simp) ryz⟩
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega))
    fun s₇ ⟨ex, ey, ez, k₇, O₇⟩ => ?_)
  simp only [ptAt] at ex ey ez
  rw [hm₆] at ex ey ez
  have esi₇ : s₇.gpr .esi = BitVec.ofNat 32 (j - 1) := by rw [k₇.1 _ (by decide), k₆.1 _ (by decide), esi₅]
  have U₅₇ : Unch base [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)] s₅.mem s₇.mem := by
    rw [← hm₆]; exact Outs.unch O₇
  refine wp_testCounter (by omega) esi₇ fun s₈ f₈ z₈ =>
    WP.block_nil ⟨⟨?_, by rw [f₈.gpr, esi₇], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, z₈⟩
  · exact (hs₆.of_keeps k₇ (by decide)).of_keeps (f₈.keeps []) (by decide)
  · exact (hI.keep.trans K₅).trans ((k₆.mono (by decide)).trans ((k₇.mono (by decide)).trans (f₈.keeps _)))
  · rw [f₈.mem]
    exact (hU₅.trans U₅₇).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ (List.mem_append_left _ (mem_ladW_R w hw))
  · rw [f₈.mem]
    have hmo := hL.lay.mo
    have mx := hmo L.R.x (ladPts_slots L _ (by simp))
    have my := hmo L.R.y (ladPts_slots L _ (by simp))
    have mz := hmo L.R.z (ladPts_slots L _ (by simp))
    have hpm := hP.mo
    have hwm := hW.mo
    exact hI.mod.unch (U₁₅r.trans U₅₇) (by apart_rangesW) (by have := hI.scr.nowrap; omega)
  · rw [f₈.mem]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex]; split
      · exact l5x
      · rw [p5x]; exact l3x
    · rw [ey]; split
      · exact l5y
      · rw [p5y]; exact l3y
    · rw [ez]; split
      · exact l5z
      · rw [p5z]; exact l3z
  · have hq := hstep (j - 1) (by omega) _ _ _ _ _ _ _ _ _ (by rw [Nat.sub_add_cancel hj]; exact hI.q) E₃.symm E₅.symm
    have hx : tmv C L.M.n base s₈ L.R.x = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base (Spec.Weierstrass.Point.oAt L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base (Spec.Weierstrass.Point.oAt L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [f₈.mem, ex]; split
      · rfl
      · rw [p5x]
    have hy : tmv C L.M.n base s₈ L.R.y = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base
          (Spec.Weierstrass.Point.oAt L.M.n + Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base
          (Spec.Weierstrass.Point.oAt L.M.n + Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [f₈.mem, ey]; split
      · rfl
      · rw [p5y]
    have hz : tmv C L.M.n base s₈ L.R.z = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base
          (Spec.Weierstrass.Point.oAt L.M.n + 2 * Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base
          (Spec.Weierstrass.Point.oAt L.M.n + 2 * Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [f₈.mem, ez]; split
      · rfl
      · rw [p5z]
    rw [hx, hy, hz]
    exact hq
  · rw [f₈.mem]
    exact cp₅.keep hk3 hk6 U₅₇ (by apart_ranges)
  · have K₇ : Keeps [.eax, .ecx, .edx] s₅ s₈ :=
      ((k₆.mono (by decide)).trans (k₇.mono (by decide))).trans (f₈.keeps _)
    refine arg₅.keep (K₇.1 _ (by decide)) (K₇.1 _ (by decide)) K₇.2.1 K₇.2.2 ?_
    rw [f₈.mem]
    exact (frame_of_outs U₅₇ (by apart_ranges)).mono (by simp)

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`; only `powClob` and `ladWp` change. As
`ladder_ok`, for the slots below the point functions' (`LadPt`) and the
caller's argument holding `edi` (`LadArg`, which it keeps) if it calls them. -/
theorem ladderP_ok {k : Nat} {Q : Nat → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Prop}
    (hL : LadLay L size) (hW : LadWk L F C.p size wk) (hP : 3 ≤ L.M.n ∧ L.M.n ≤ 6 → LadPt L)
    (hp : UnitMod C.p (2 ^ (64 * L.M.n))) {s : State} (hs : Scr s base size)
    (hA : 3 ≤ L.M.n ∧ L.M.n ≤ 6 → LadArg s base ao) (hM : ModOkW L.M size C.p s.mem base)
    (hlt : ∀ x ∈ ladR L, wordsVal s.mem base x L.M.n < C.p) (hstep : Step L C base s k Q)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladderP L F ao) s fun s' => Keeps powClob s s' ∧ Unch base (ladWp L wk) s.mem s'.mem ∧
      ModOkW L.M size C.p s'.mem base ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) ∧
      (3 ≤ L.M.n ∧ L.M.n ≤ 6 → LadArg s' base ao) := by
  unfold ladderP ladWp ptW
  by_cases hk : 3 ≤ L.M.n ∧ L.M.n ≤ 6
  swap
  · simp only [hk, ↓reduceIte, List.append_nil]
    exact WP.mono (ladder_ok hL hW hp hs hM hlt hstep hR hbits) fun _ ⟨a, b, c, d, e⟩ =>
      ⟨a, b, c, d, e, fun h => h.elim⟩
  simp only [hk]
  have hPt := hP hk
  have hA₀ := hA hk
  have hk3 := hk.1
  have hk6 := hk.2
  have hl := lay_nums hk3 hk6
  have hsz : size = 8192 := hW.size
  have hn := hs.nowrap
  have rx : L.R.x + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladPts_slots L _ (by simp))
  have ry : L.R.y + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladPts_slots L _ (by simp))
  have rz : L.R.z + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladPts_slots L _ (by simp))
  have gx : L.G.x + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have gy : L.G.y + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have gz : L.G.z + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have ga : L.S.a + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have gb : L.S.b3 + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  refine WP.seq ?_
  rw [ladderSetup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  -- `Q = G`, `a`, `3b`.
  refine WP.mono (copyPt_ok hs (n := L.M.n) (o := ptAt L.M.n (Spec.Weierstrass.Point.qAt L.M.n)) (a := L.G)
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
    (by simp only [ptAt]; omega)
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega))
    fun s₁ ⟨gx₁, gy₁, gz₁, k₁, O₁⟩ => ?_
  simp only [ptAt] at gx₁ gy₁ gz₁ O₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * L.M.n) hs₁ (o := Spec.Weierstrass.Point.aAt L.M.n) (a := L.S.a) (by omega) (by omega)
    (by omega)) fun s₂ ⟨a₂, k₂, O₂⟩ => ?_
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32] at a₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * L.M.n) hs₂ (o := Spec.Weierstrass.Point.b3At L.M.n) (a := L.S.b3) (by omega) (by omega)
    (by omega)) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32] at b₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine wp_movS rfl fun s₄ u₄ _ => WP.block_nil ?_
  have hm₄ : s₄.mem = s₃.mem := u₄.mem
  have U₂ : Unch base [(Spec.Weierstrass.Point.aAt L.M.n, 4 * (2 * L.M.n))] s₁.mem s₂.mem := O₂.unch
  have U₃ : Unch base [(Spec.Weierstrass.Point.b3At L.M.n, 4 * (2 * L.M.n))] s₂.mem s₃.mem := O₃.unch
  have U₁₃r : Unch base ([(Spec.Weierstrass.Point.qAt L.M.n, 8 * L.M.n),
      (Spec.Weierstrass.Point.qAt L.M.n + Spec.Weierstrass.Point.elemBytes L.M.n, 8 * L.M.n),
      (Spec.Weierstrass.Point.qAt L.M.n + 2 * Spec.Weierstrass.Point.elemBytes L.M.n, 8 * L.M.n)] ++
      ([(Spec.Weierstrass.Point.aAt L.M.n, 4 * (2 * L.M.n))] ++
        [(Spec.Weierstrass.Point.b3At L.M.n, 4 * (2 * L.M.n))])) s.mem s₄.mem := by
    rw [hm₄]; exact (Outs.unch O₁).trans (U₂.trans U₃)
  have U₁₃ : Unch base [(Spec.Weierstrass.Point.oAt L.M.n, 4096 - Spec.Weierstrass.Point.oAt L.M.n)] s.mem s₄.mem :=
    U₁₃r.cover (by in_pt)
  have K₄ : Keeps powClob s s₄ := (k₁.mono (by decide)).trans <| (k₂.mono (by decide)).trans <|
    (k₃.mono (by decide)).trans (u₄.keeps.mono (by decide))
  have low : ∀ {x}, x + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n →
      wordsVal s₄.mem base x L.M.n = wordsVal s.mem base x L.M.n := fun hx =>
    U₁₃.wordsVal (by apart_ranges) (by omega)
  refine countLoop_ok (Inv := fun j s' => LadInvP L wk C base size ao Q s s' j) (n := L.nbits)
    (fun j s' h1 h2 hi => ladderPBody_ok hL hW hk6 hPt (fun x hx => hlt x (mem_ladRo_ladR hx))
      hstep hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, hi.q, fun _ => hi.arg⟩) hL.nbits.1
    ⟨hs.of_keeps K₄ (by decide), u₄.gpr, K₄, U₁₃.mono fun w hw => List.mem_append_right _ hw,
      hM.unch U₁₃ (by have := hPt.mo; apart_ranges) (by omega), fun x hx => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [low rx]; exact hlt _ (by simp [ladR])
    · rw [low ry]; exact hlt _ (by simp [ladR])
    · rw [low rz]; exact hlt _ (by simp [ladR])
  · show Q L.nbits (toM _ _ _) (toM _ _ _) (toM _ _ _)
    rw [low rx, low ry, low rz]
    exact hR
  · have k₂₄ : Unch base [(Spec.Weierstrass.Point.aAt L.M.n, 4 * (2 * L.M.n)),
        (Spec.Weierstrass.Point.b3At L.M.n, 4 * (2 * L.M.n))] s₁.mem s₄.mem := by
      rw [hm₄]; exact U₂.trans U₃
    have k₃₄ : Unch base [(Spec.Weierstrass.Point.b3At L.M.n, 4 * (2 * L.M.n))] s₂.mem s₄.mem := by
      rw [hm₄]; exact U₃
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [k₂₄.wordsVal (by apart_ranges) (by omega), gx₁]
    · rw [k₂₄.wordsVal (by apart_ranges) (by omega), gy₁]
    · rw [k₂₄.wordsVal (by apart_ranges) (by omega), gz₁]
    · rw [k₃₄.wordsVal (by apart_ranges) (by omega), a₂, (Outs.unch O₁).wordsVal (by apart_ranges) (by omega)]
    · rw [hm₄, b₃, U₂.wordsVal (by apart_ranges) (by omega), (Outs.unch O₁).wordsVal (by apart_ranges) (by omega)]
  · exact hA₀.keep (K₄.1 _ (by decide)) (K₄.1 _ (by decide)) K₄.2.1 K₄.2.2
      ((frame_of_outs U₁₃r (by apart_ranges)).mono (by simp))

end body

end VG.Proof.Weierstrass.X86.Point
