module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
public import VerifiedGarbage.Proof.Rsa.Arm.MulMod
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
public import VerifiedGarbage.Proof.Bignum.Arm.Stack
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # An RSA key on ARMv7: the frame's words, and products

`KS.ldrSp`: a frame word, which the body never writes. `St.pmulFrom`:
`[o] := ([c] + ([b] mod 2^n) [a]) mod [aMod]` by `mulMod` over `n` bits,
through its arrays.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {P : KP} {σ s : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- A frame word keeps its value. -/
theorem KS.fwEq (h : KS P σ A live V ls s) {o : Nat} (ho' : o + 4 ≤ 112) : fw s.mem P o = fw σ.mem P o := by
  have pre := h.pre
  refine h.frame.readW (r := ⟨off (State.addr P.sp) o, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact pre.sF.symm.sub_left (Offset.sub_base _ ho')

/-- A frame word is readable. -/
theorem In.fwRead (pre : In P σ) {o : Nat} (ho' : o + 4 ≤ 112) (h4 : o % 4 = 0) :
    InRegions (σ.rd ++ σ.wr) (off (State.addr P.sp) o) 4 := by
  have spf := pre.spFit
  rcases (by omega : o + 4 ≤ 56 ∨ 56 ≤ o) with c | c
  · exact ⟨⟨State.addr P.sp, 56⟩, List.mem_append_right _ (by rw [pre.wr]; simp),
      Offset.contains_base _ c (by omega)⟩
  · have read := CallLay.inRegions_sub pre.rdA (off := o - 56) (l := 4) (by omega) (by decide)
    rwa [show off (State.addr P.sp) 56 + BitVec.ofNat 64 (o - 56) = off (State.addr P.sp) o by
      simp only [off]; rw [Offset.add_add]; congr 2; omega] at read

/-- `ldr t, [sp, #o]` of a frame word. -/
theorem KS.ldrSp (h : KS P σ A live V ls s) {o : Nat} (ho' : o + 4 ≤ 112) (h4 : o % 4 = 0) {t : Reg} {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' t (fw σ.mem P o) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q := by
  have pre := h.pre
  have spf := pre.spFit
  have ea : State.addr (s.sp + BitVec.ofNat 32 o) = off (State.addr P.sp) o := by
    rw [h.sp, pre.sp]; exact addr_add (by omega)
  refine wp_loadStack (by omega) ea ?_ fun s' u => k s' (by rw [← h.fwEq ho']; exact u)
  rw [h.rd, h.wr]
  exact pre.fwRead ho' h4

end

section
variable {P : KP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}



/-- `r6 := 8 p_len`. -/
theorem St.pcnt8 : VP (St P E A L V LS) (.block cnt8)
    (fun σ s => St P E A L V LS σ s ∧ s.gpr .r6 = BitVec.ofNat 32 (8 * P.K)) := by
  show VP _ (.block (([(Reg.r6, aoPl)].map fun p => Instr.ldrSp p.1 p.2) ++ [.mov .r6 (.shifted .r6 .lsl 3)])) _
  refine VP.block_append (G := fun σ s => St P E A L V LS σ s ∧ s.gpr .r6 = BitVec.ofNat 32 P.K) ?_ ?_
  · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
    · refine h.ldrSp (o := aoPl) (by decide) (by decide) fun t u => WP.block_nil ⟨⟨e, h.of_rest (u.rest (ws := [.r6]) (by simp))
        u.mem, hw.of_upd u (by decide) (by decide) (by decide)⟩, by rw [u.gpr, h.pre.aPl]⟩
  · refine VP.taint [.r6] lsl3_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨e, h, hw⟩, r6⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
    · refine wp_mov (op2_lsl (by decide)) fun t u => WP.block_nil ⟨⟨e, h.of_rest (u.rest (ws := [.r6]) (by simp))
        u.mem, hw.of_upd u (by decide) (by decide) (by decide)⟩, ?_⟩
      have := h.pre.k2
      rw [u.gpr, r6]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega

/-- `r6 := 64`. -/
theorem St.pmov64 : VP (St P E A L V LS) (.block [.mov .r6 (.imm 64)])
    (fun σ s => St P E A L V LS σ s ∧ s.gpr .r6 = BitVec.ofNat 32 64) :=
  VP.taint [] mov64_taint (fun _ _ _ _ _ _ r hr => absurd hr List.not_mem_nil) fun σ s ⟨e, h, hw⟩ =>
    wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ⟨⟨e, h.of_rest (u.rest (ws := [.r6]) (by simp))
      u.mem, hw.of_upd u (by decide) (by decide) (by decide)⟩, by rw [u.gpr]; rfl⟩

/-- The arrays `mulMod` writes. -/
abbrev mArrs : List Nat := mulArrs aMy aMx aMa aMt


/-- `mulMod` over `n` bits: `[aMa] := ([aMa] + ([aMy] mod 2^n) [aMx]) mod [aMod]`. -/
theorem St.pmulMod {L0 : List Nat} {n : Nat} (hn : ∀ σ, In P σ → 0 < n ∧ n < 2 ^ 32) (hZ : aZero ∈ L0) (hM : aMod ∈ L0)
    (hL0 : ∀ j ∈ L0, j ∉ mArrs) (hLS : ∀ d ∈ LS, d ∉ [sB, sC])
    (hv : ∀ σ, E σ → A σ aZero = 0 ∧ A σ aMa < A σ aMod ∧ A σ aMx < A σ aMod ∧ 2 * A σ aMod ≤ 2 ^ (32 * P.W)) :
    VP (fun σ s => St P E A (aMa :: aMx :: aMy :: L0) V LS σ s ∧ s.gpr .r6 = BitVec.ofNat 32 n)
      (mulMod aZero aMy aMx aMa aMod aMt)
      (St P E (fun σ => upd (A σ) aMa ((A σ aMa + A σ aMy % 2 ^ n * A σ aMx) % A σ aMod)) (aMa :: L0) V LS) := by
  refine VP.taint [.r6, .r7, .r8, .r9] mulMod_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_)
    fun σ s ⟨⟨e, h, hw⟩, r6⟩ => ?_
  · have w₁ := h₁.1.2.2; have w₂ := h₂.1.2.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2, h₂.2]
    · rw [w₁.r7, w₂.r7]
    · rw [w₁.r8, w₂.r8]
    · rw [w₁.r9, w₂.r9]
  · obtain ⟨vZ, vA, vX, vM⟩ := hv σ e
    refine WP.mono (mulMod_ok hw (by decide) (by decide) (hn σ h.pre).1 (hn σ h.pre).2 r6)
      fun t ⟨ht, k, r, v⟩ => ⟨e, ?_, ht⟩
    have g : ∀ j ∈ aMa :: aMx :: aMy :: L0, num s.mem P.B P.W j = A σ j := fun j hj => h.arrs j hj
    have hds : ∀ d ∈ [sB, sC], SlotOk d := by decide
    refine h.core k (by decide) hds r.sp r.rd r.wr (fun j hj => ?_) (h.sl_keep k hds hLS)
      (fun j hj => ?_) h.ls_ok
    · dsimp only
      rcases List.mem_cons.mp hj with rfl | hj'
      · rw [upd_self]
        rw [g aMa (by simp), g aMy (by simp), g aMx (by simp), g aMod (by simp [hM])] at v
        exact v (by rw [g aZero (by simp [hZ])]; exact vZ) vA vX vM
      · have hjm : j ≠ aMa := fun x => hL0 j hj' (by rw [x]; decide)
        rw [upd_ne _ _ hjm, k.num (fun i hi ei => by subst ei; exact hL0 _ hj' hi) (fun d hd => (hds d hd).1)
          (h.pre.fit (h.live_lt j (by simp [hj'])))]
        exact g j (by simp [hj'])
    · rcases List.mem_cons.mp hj with rfl | hj'
      · decide
      · exact h.live_lt j (by simp [hj'])

/-- `mulFrom o a b c k`: `[o] := ([c] + ([b] mod 2^n) [a]) mod [aMod]`, `k` setting `r6 := n`. -/
theorem St.pmulFrom {o a b c n : Nat} {k : List Instr}
    (cy : Cert (copy aMy b)) (cx : Cert (copy aMx a)) (ca : Cert (copy aMa c)) (co : Cert (copy o aMa))
    (hk : ∀ {A' : State → Nat → Nat} {L' : List Nat}, VP (St P E A' L' V LS) (.block k)
      (fun σ s => St P E A' L' V LS σ s ∧ s.gpr .r6 = BitVec.ofNat 32 n))
    (hn : ∀ σ, In P σ → 0 < n ∧ n < 2 ^ 32) (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hZ : aZero ∈ L) (hM : aMod ∈ L)
    (ho : o < nArr) (hom : o ∉ mArrs) (hL : ∀ j ∈ L, j ∉ mArrs) (hLS : ∀ d ∈ LS, d ∉ [sB, sC])
    (hv : ∀ σ, E σ → A σ aZero = 0 ∧ A σ c < A σ aMod ∧ A σ a < A σ aMod ∧ 2 * A σ aMod ≤ 2 ^ (32 * P.W)) :
    VP (St P E A L V LS) (mulFrom o a b c k)
      (St P E (fun σ => upd (A σ) o ((A σ c + A σ b % 2 ^ n * A σ a) % A σ aMod)) (o :: L) V LS) := by
  have nb : b ∉ mArrs := hL b hb
  have na : a ∉ mArrs := hL a ha
  have nc : c ∉ mArrs := hL c hc
  simp only [mulFrom, seqs]
  let A1 := fun σ => upd (A σ) aMy (A σ b)
  let A2 := fun σ => upd (A1 σ) aMx (A σ a)
  let A3 := fun σ => upd (A2 σ) aMa (A σ c)
  have e1 : ∀ σ j, j ∈ L → A1 σ j = A σ j := fun σ j hj => upd_ne _ _ fun x => hL j hj (by rw [x]; decide)
  have e2 : ∀ σ j, j ∈ L → A2 σ j = A σ j := fun σ j hj => by
    show upd (A1 σ) aMx _ j = _; rw [upd_ne _ _ fun x => hL j hj (by rw [x]; decide), e1 σ j hj]
  have e3 : ∀ σ j, j ∈ L → A3 σ j = A σ j := fun σ j hj => by
    show upd (A2 σ) aMa _ j = _; rw [upd_ne _ _ fun x => hL j hj (by rw [x]; decide), e2 σ j hj]
  refine VP.seq (St.pcopy cy (by decide) hb (fun x => nb (by rw [← x]; decide))) ?_
  have u2 : ∀ σ j, upd (upd (A σ) aMy (A σ b)) aMx (upd (A σ) aMy (A σ b) a) j = A2 σ j := fun σ j => by
    show _ = upd (A1 σ) aMx _ j
    by_cases x : j = aMx
    · subst x; rw [upd_self, upd_self]; exact e1 σ a ha
    · rw [upd_ne _ _ x, upd_ne _ _ x]
  have u3 : ∀ σ j, upd (A2 σ) aMa (A2 σ c) j = A3 σ j := fun σ j => by
    show _ = upd (A2 σ) aMa _ j
    by_cases x : j = aMa
    · subst x; rw [upd_self, upd_self]; exact e2 σ c hc
    · rw [upd_ne _ _ x, upd_ne _ _ x]
  refine VP.seq (G := St P E A2 (aMx :: aMy :: L) V LS) ((St.pcopy cx (by decide) (List.mem_cons_of_mem _ ha)
    (fun x => na (by rw [← x]; decide))).mono (fun _ _ h => h) fun σ s h => h.mono
      (fun j hj => ⟨hj, u2 σ j⟩) (fun d hd => ⟨hd, rfl⟩)) ?_
  refine VP.seq (G := St P E A3 (aMa :: aMx :: aMy :: L) V LS) ((St.pcopy ca (by decide)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)) (fun x => nc (by rw [← x]; decide))).mono (fun _ _ h => h)
      fun σ s h => h.mono (fun j hj => ⟨hj, u3 σ j⟩) (fun d hd => ⟨hd, rfl⟩)) ?_
  refine VP.seq hk (VP.seq (St.pmulMod (L0 := L) hn hZ hM hL hLS fun σ e => ?_) ?_)
  · obtain ⟨vZ, vC, vA, vM⟩ := hv σ e
    refine ⟨by rw [e3 σ _ hZ]; exact vZ, ?_, ?_, ?_⟩
    · show upd (A2 σ) aMa _ aMa < _; rw [upd_self, e3 σ _ hM]; exact vC
    · show upd (A2 σ) aMa _ aMx < _; rw [upd_ne _ _ (by decide), e3 σ _ hM]
      show upd (A1 σ) aMx _ aMx < _; rw [upd_self]; exact vA
    · rw [e3 σ _ hM]; exact vM
  · refine (St.pcopy co ho (by simp) (fun x => hom (by rw [x]; decide))).mono (fun _ _ h => h)
      fun σ s h => h.mono (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
    · rcases List.mem_cons.mp hj with rfl | hj'
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj')
    · by_cases x : j = o
      · subst x
        simp only [upd_self]
        have y3 : A3 σ aMy = A σ b := by
          show upd (A2 σ) aMa _ aMy = _; rw [upd_ne _ _ (by decide)]
          show upd (A1 σ) aMx _ aMy = _; rw [upd_ne _ _ (by decide)]
          show upd (A σ) aMy _ aMy = _; rw [upd_self]
        have x3 : A3 σ aMx = A σ a := by
          show upd (A2 σ) aMa _ aMx = _; rw [upd_ne _ _ (by decide)]
          show upd (A1 σ) aMx _ aMx = _; rw [upd_self]
        have a3 : A3 σ aMa = A σ c := by show upd (A2 σ) aMa _ aMa = _; rw [upd_self]
        rw [y3, x3, a3, e3 σ _ hM]
      · have hj' := (List.mem_cons.mp hj).resolve_left x
        rw [upd_ne _ _ x, upd_ne _ _ x, upd_ne _ _ fun y => hL j hj' (by rw [y]; decide), e3 σ j hj']

end

end VG.Proof.RsaKeyGen.Arm.Key
