import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombAdd

/-!
# The `zmm` comb: the `ymm` blocks of an entry, alone

The `zmm` comb's selection leaves each half's rows of the entry in
`ymm11–ymm14` and its sign's mask in `ymm15` itself, so its translated blocks
are `esplit` (`eload` without the rows' setup) and `vnegBody` (`vneg` without
the mask's): their lemmas, as `eload_wp` and `vneg_wp`.
-/

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519.X86_64.Ifma
open VG.Impl.X25519.X86_64.Ifma (KM kb ord)
open VG.Proof.X25519.X86_64.Ifma (Sym T Env Bnds EnvOK symOf symOf_eq slotv CConsts envOK_of envOf envOf_m
  envOf_v lt64 run_ok limbNat Ctx xor_mask pick2_tt pick2_ff vm kb_m kbv lanes)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw sel4)
open VG.Proof.X25519.X86_64.Ifma (fe5 fe5_congr fe5_carry fe5_sub carryF_wp vm_gpr vm_rd vm_wr)
open VG.Proof.X25519.X86_64 (Outside)

/-! ## The entry's limbs -/

def esplitS : Sym := symOf esplit

/-- Word `k` of row `l` of the entry: quadword `k` of `ymm (11 + l)`. -/
def srow (E : VG.Proof.X25519.X86_64.Ifma.Env) (l k : Nat) : Nat := E.v (11 + l) k

theorem esplitS_regs (E : VG.Proof.X25519.X86_64.Ifma.Env) : ∀ j < 5, ∀ l < 4, (esplitS.reg (5 + j)).nat E l =
    limbNat (srow E l) (E.m KM l) j := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

def esplitB : Bnds :=
  ⟨fun _ => 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1, fun d => if d = KM then 2 ^ 51 - 1 else 2 ^ 64 - 1,
    fun _ => 0⟩

theorem esplitS_ok : ∀ j < 5, ∀ l < 4, (esplitS.reg (5 + j)).ok esplitB l = true ∧
    (esplitS.reg (5 + j)).bnd esplitB l < 2 ^ 52 := by
  decide +kernel

theorem esplitS_keep : ∀ r < 5, esplitS.reg r = .reg r := by decide +kernel
theorem esplitS_st : esplitS.st = [] := by decide +kernel

theorem esplit_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : CConsts s.mem base) :
    WP isa (.block esplit) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 5 l i = limbNat (srow (envOf s) l) (2 ^ 51 - 1) i ∧
        lanes s' 5 l i < 2 ^ 52) ∧
      (∀ r < 5, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE : EnvOK s esplitB := envOK_of hs (fun _ _ _ => lt64 _) (fun _ => rfl) (fun d l hl => by
      simp only [esplitB]
      split
      · subst_vars; rw [hk.km l hl]
      · exact lt64 _) (fun _ _ _ => Nat.zero_le _)
  have e : Sym.init.run esplit = some esplitS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ⟨h.eq, by rw [h.mem, esplitS_st]; rfl, fun l hl i hi => ?_,
    fun r hr l hl => h.keep (by omega) hl (esplitS_keep r hr)⟩
  obtain ⟨o, b⟩ := esplitS_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega) hl o
  simp only [lanes] at e ⊢
  refine ⟨?_, by omega⟩
  rw [e, esplitS_regs _ i hi l hl, envOf_m hs, hk.km l hl]

/-! ## The negation -/

def vnegBodyS : Sym := symOf vnegBody

theorem vnegBodyS_regs : ∀ j < 5, vnegBodyS.reg (5 + j) = .xor (.reg (5 + j))
    (.and (.xor (.blend (.perm (.reg (5 + j)) (ord 1 0 2 3).toNat) (.sub (.ld (kb j)) (.reg (5 + j)))
      (Impl.X25519.X86_64.Ifma.lanes false false true false).toNat) (.reg (5 + j))) (.reg 15)) := by
  decide +kernel

theorem vnegBodyS_keep : ∀ r < 5, vnegBodyS.reg r = .reg r := by decide +kernel
theorem vnegBodyS_st : vnegBodyS.st = [] := by decide +kernel

theorem vnegBody_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : CConsts s.mem base) {b : Bool} (hm : ∀ k < 4, qw s (xr 15) k = VG.Proof.X25519.X86_64.mask b)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 5 l i ≤ kbv i) :
    WP isa (.block vnegBody) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 5 l i = if b then negL (lanes s 5) l i else lanes s 5 l i) ∧
      (∀ r < 5, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run vnegBody = some vnegBodyS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ⟨h.eq, by rw [h.mem, vnegBodyS_st]; rfl, fun l hl i hi => ?_,
    fun r hr l hl => h.keep (by omega) hl (vnegBodyS_keep r hr)⟩
  have hq := h.reg (xr (5 + i)) l hl
  rw [VG.Proof.X25519.X86_64.Ifma.xi_xr _ (by omega), vnegBodyS_regs i hi] at hq
  simp only [lanes]
  rw [hq]
  simp only [T.eval]
  rw [hm l hl, xor_mask]
  cases b
  · rfl
  · have hkb : ∀ q < 4, (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (kb i + 8 * q)) 64).toNat = kbv i :=
      fun q hq' => by rw [hs]; exact kb_m hk hq'
    simp only [↓reduceIte]
    have hb : ∀ q < 4, ((Impl.X25519.X86_64.Ifma.lanes false false true false).toNat.testBit (2 * q),
        (Impl.X25519.X86_64.Ifma.lanes false false true false).toNat.testBit (2 * q + 1)) =
        (decide (q = 2), decide (q = 2)) := by decide
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      have b := hb _ hl <;> simp only [Prod.mk.injEq] at b <;> rw [b.1, b.2] <;>
      simp only [decide_true, decide_false, Nat.reduceEqDiff]
    · rw [pick2_ff, show sel4 (ord 1 0 2 3).toNat 0 = 1 from by decide]; rfl
    · rw [pick2_ff, show sel4 (ord 1 0 2 3).toNat 1 = 0 from by decide]; rfl
    · rw [pick2_tt, BitVec.toNat_sub_of_le, hkb 2 (by decide)]
      · rfl
      · rw [BitVec.le_def, hkb 2 (by decide)]; exact hx 2 (by decide) i hi
    · rw [pick2_ff, show sel4 (ord 1 0 2 3).toNat 3 = 3 from by decide]; rfl


/-! ## The addition of an entry from its limbs -/

/-- `vnegBody`, the carry and `vadd`: the entry in the lanes of `ymm5–ymm9`, negated if the
mask in `ymm15` is all ones, added to the point in those of `ymm0–ymm4` (`ventry_wp` from
`eload`'s limbs). -/
theorem ventryN_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : EConsts s.mem base) (hx : Small s) {b : Bool}
    (hm : ∀ k < 4, qw s (xr 15) k = VG.Proof.X25519.X86_64.mask b)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) :
    WP isa (.block (vnegBody ++ VG.Impl.X25519.X86_64.Ifma.carry (5 + ·) ++ vadd)) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 1024 320 s.mem s'.mem ∧ Small s' ∧
      lanePt s' = vAddPt (lanePt s) (negIf b (lanePt5 s)) := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (vnegBody_wp hs hc hk.toCConsts hm
    fun l hl i hi => by have := hy l hl i hi; have := kbv_ge i; omega) fun s₂ ⟨v₂, m₂, u₂, k₂⟩ => ?_
  have hs₂ : s₂.gpr .rdi = base := by rw [vm_gpr v₂]; exact hs
  have hc₂ : Ctx s₂ := by intro d hd; rw [vm_gpr v₂, vm_wr v₂]; exact hc d hd
  have hk₂ : EConsts s₂.mem base := by rw [m₂]; exact hk
  have b₂ : ∀ l < 4, ∀ i < 5, lanes s₂ 5 l i < 2 ^ 63 := fun l hl i hi => by
    rw [u₂ l hl i hi]
    have h0 := hy 0 (by decide) i hi; have h1 := hy 1 (by decide) i hi
    have h3 := hy 3 (by decide) i hi; have := hy l hl i hi
    have := kbv_ge i
    have : kbv i < 2 ^ 63 := by simp only [kbv]; split <;> omega
    split
    · rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> simp only [negL] <;> omega
    · omega
  have f₂ : ∀ l < 4, fe5 (lanes s₂ 5 l) = [(negIf b (lanePt5 s)).X, (negIf b (lanePt5 s)).Y,
      (negIf b (lanePt5 s)).Z, (negIf b (lanePt5 s)).T].getD l 0 := fun l hl => by
    rw [fe5_congr (fun i hi => u₂ l hl i hi)]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, negIf, lanePt5]
      rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl
    · simp only [↓reduceIte, negIf, lanePt5]
      rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl
      · rfl
      · rfl
      · rw [show fe5 (fun i => negL (lanes s 5) 2 i) = fe5 (fun _ => 0) - fe5 (lanes s 5 2) from
          fe5_sub (fun i _ => (Nat.zero_add _).symm)
            (fun i hi => by have := hy 2 (by decide) i hi; have := kbv_ge i; omega)]
        rfl
      · rfl
  rw [WP.block_append_iff]
  refine WP.mono (carryF_wp hs₂ hc₂ hk₂.toCConsts b₂) fun s₃ ⟨v₃, m₃, u₃, k₃⟩ => ?_
  have hs₃ : s₃.gpr .rdi = base := by rw [vm_gpr v₃]; exact hs₂
  have hc₃ : Ctx s₃ := by intro d hd; rw [vm_gpr v₃, vm_wr v₃]; exact hc₂ d hd
  have hk₃ : EConsts s₃.mem base := by rw [m₃]; exact hk₂
  have l₃ : ∀ l < 4, ∀ i < 5, lanes s₃ 0 l i = lanes s 0 l i := fun l hl i hi => by
    simp only [lanes, Nat.zero_add]
    rw [k₃ i (by omega) (by omega) (by omega) l hl, k₂ i (by omega) l hl]
  refine WP.mono (vadd_wp hs₃ hc₃ hk₃ (fun l hl i hi => by rw [l₃ l hl i hi]; exact hx l hl i hi)
    (fun l hl i hi => (u₃ l hl i hi).2)) fun t ⟨tg, trd, twr, ho, tsm, tp⟩ => ?_
  refine ⟨by rw [tg, vm_gpr v₃, vm_gpr v₂], by rw [trd, vm_rd v₃, vm_rd v₂],
    by rw [twr, vm_wr v₃, vm_wr v₂], by rw [m₃, m₂] at ho; exact ho, tsm, ?_⟩
  rw [tp]
  have p₃ : lanePt s₃ = lanePt s := by
    simp only [lanePt]; rw [fe5_congr (l₃ 0 (by decide)), fe5_congr (l₃ 1 (by decide)),
      fe5_congr (l₃ 2 (by decide)), fe5_congr (l₃ 3 (by decide))]
  have e₃ : ∀ l < 4, fe5 (lanes s₃ 5 l) = fe5 (lanes s₂ 5 l) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₃ l hl i hi).1), fe5_carry _ (b₂ l hl 4 (by decide))]
  have q₃ : lanePt5 s₃ = negIf b (lanePt5 s) := by
    conv => lhs; simp only [lanePt5]
    rw [e₃ 0 (by decide), e₃ 1 (by decide), e₃ 2 (by decide), e₃ 3 (by decide), f₂ 0 (by decide),
      f₂ 1 (by decide), f₂ 2 (by decide), f₂ 3 (by decide)]
    rfl
  rw [p₃, q₃]

end VG.Proof.Ed25519.X86_64.Zmm
