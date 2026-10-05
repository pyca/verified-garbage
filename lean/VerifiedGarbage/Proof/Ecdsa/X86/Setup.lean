import VerifiedGarbage.Proof.Ecdsa.X86.Layout
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen

/-!
# ECDSA on x86 (32-bit): the setup

`Cfg.setupWith A` reads the working space's base from its argument `A.sc` and saves
`ebx`, `esi`, `edi` and `ebp` at its start (`setupSaves_ok`), moves the base
to `edi`, reads `k`, `d` and the hash (`len` bytes each) big-endian into
their slots through `ebx` (`setupLoad_ok`, once each, after reading the
pointer: `argLoad_ok`), shifts the slot `A.hs` holding a hash
(`setupShift_ok`), stores the constants (`setupConsts_ok`, by induction on the
list) and sets the flag to all ones: `setup_ok`, the state `SetupPost`
describes.
-/

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

/-! ## The arguments -/

/-- An argument, in memory that changed only in the working space. -/
theorem arg_keep {s₀ : State} {q : Addr} {m : Mem} (ho : Outside q 0 size s₀.mem m) {i : Nat}
    (hd : Region.Disjoint ⟨argAddr s₀ i, 4⟩ ⟨q, size⟩) : m.readW (argAddr s₀ i) 32 = arg s₀ i := by
  rw [arg, ← BitVec.add_zero (argAddr s₀ i)]
  exact readW32_keep (d := 0) fun j hj => keep_of_disjoint' ho hd (by decide) (by omega) (by decide)

/-- `r = ` argument `i`, read in memory that changed only in the working space. -/
theorem argLoad_ok {s₀ t : State} {q : Addr} {i : Nat} (hin : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4)
    (hd : Region.Disjoint ⟨argAddr s₀ i, 4⟩ ⟨q, size⟩) (hesp : t.gpr .esp = s₀.gpr .esp)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr) (ho : Outside q 0 size s₀.mem t.mem) :
    readSrc t (.mem (Cfg.argOp i)) = some (arg s₀ i) := by
  show t.load32 (addr (t.gpr .esp) (4 + 4 * i)) = _
  rw [hesp, ← argAddr_eq, State.load32, hrw, ite_eq_left_iff.mpr fun h => absurd hin h, arg_keep ho hd]

/-- `argLoad_ok` for an argument the setup reads. -/
theorem SetupPre.argLoad {c : Cfg} {A : Args} {s₀ t : State} (hp : SetupPre c A s₀)
    (hesp : t.gpr .esp = s₀.gpr .esp) (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr)
    (ho : Outside (ptr s₀ A.sc) 0 size s₀.mem t.mem) {i : Nat} (hi : i ∈ A.idx) :
    readSrc t (.mem (Cfg.argOp i)) = some (arg s₀ i) :=
  argLoad_ok (hp.arg_in i hi) (hp.arg_sc i hi) hesp hrw ho

/-! ## Saving the callee-saved registers -/

/-- `[eax + d] = r` for the saved registers, with `eax` the working space. -/
theorem setupSaves_ok {s : State} {base : Addr} (hb : (s.gpr .eax).setWidth 64 = base)
    (hfit : (s.gpr .eax).toNat + size ≤ 2 ^ 32) (hw : (⟨base, size⟩ : Region) ∈ s.wr) :
    WP isa (.block Cfg.saveCode) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 16 s.mem s'.mem ∧
      ∀ rd ∈ Cfg.saved, s'.mem.readW (off base rd.2) 32 = s.gpr rd.1 := by
  have hsz : size = 8192 := rfl
  have hea : ∀ (t : State) (d : Nat), t.gpr .eax = s.gpr .eax → d < 16 → t.ea (at_ .eax d) = off base d :=
    fun t d ht hd => by
      show addr (t.gpr .eax) d = _
      rw [ht, addr_eq (by omega), hb]
  have hin : ∀ (t : State) (d : Nat), t.wr = s.wr → d + 4 ≤ 16 → InRegions t.wr (off base d) 4 :=
    fun t d ht hd => by rw [ht]; exact ⟨_, hw, Offset.contains_base base (by omega) (by omega)⟩
  have hbn : base.toNat + size ≤ 2 ^ 32 := by
    rw [← hb, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hfit
  simp only [Cfg.saveCode, Cfg.saved, List.map_cons, List.map_nil]
  refine wp_storeS (hea s 0 rfl (by decide)) (hin s 0 rfl (by decide)) fun s₁ m₁ => ?_
  refine wp_storeS (hea s₁ 4 (by rw [m₁.gpr]) (by decide)) (hin s₁ 4 m₁.wr (by decide)) fun s₂ m₂ => ?_
  refine wp_storeS (hea s₂ 8 (by rw [m₂.gpr, m₁.gpr]) (by decide)) (hin s₂ 8 (by rw [m₂.wr, m₁.wr])
    (by decide)) fun s₃ m₃ => ?_
  refine wp_storeS (hea s₃ 12 (by rw [m₃.gpr, m₂.gpr, m₁.gpr]) (by decide))
    (hin s₃ 12 (by rw [m₃.wr, m₂.wr, m₁.wr]) (by decide)) fun s₄ m₄ => WP.block_nil
    ⟨by rw [m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr], by rw [m₄.rd, m₃.rd, m₂.rd, m₁.rd],
      by rw [m₄.wr, m₃.wr, m₂.wr, m₁.wr], ?_, ?_⟩
  · rw [m₄.mem, m₃.mem, m₂.mem, m₁.mem]
    exact ((((writeW32_outside _ _ _ (by omega)).mono (Nat.zero_le _) (by omega)).trans
      ((writeW32_outside _ _ _ (by omega)).mono (Nat.zero_le _) (by omega))).trans
      ((writeW32_outside _ _ _ (by omega)).mono (Nat.zero_le _) (by omega))).trans
      ((writeW32_outside _ _ _ (by omega)).mono (Nat.zero_le _) (by omega))
  · have g₃ : s₃.gpr = s.gpr := by rw [m₃.gpr, m₂.gpr, m₁.gpr]
    have g₂ : s₂.gpr = s.gpr := by rw [m₂.gpr, m₁.gpr]
    have g₁ : s₁.gpr = s.gpr := m₁.gpr
    intro rd hrd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rw [m₄.mem, m₃.mem, m₂.mem, m₁.mem]
    rcases hrd with rfl | rfl | rfl | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self32, g₁]
    · rw [Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self32, g₂]
    · rw [Mem.readW_writeW_self32, g₃]

/-! ## Reading `k`, `d` and the hash -/

/-- The `len` bytes at `p` (readable, outside the working space, and so
unchanged since `s`) to slot `i`. -/
theorem setupLoad_ok {c : Cfg} (hc : CfgOk c) {s t : State} {base : Addr} {i : Nat} {p : BitVec 32}
    (hs : Scr t base size) (hi : i < 45) (hp : t.gpr .ebx = p) (hfit : p.toNat + c.C.len ≤ 2 ^ 32)
    (hin : ∀ e, e + 4 ≤ c.C.len → InRegions (t.rd ++ t.wr) (p.setWidth 64 + BitVec.ofNat 64 e) 4)
    (hd : Region.Disjoint ⟨p.setWidth 64, c.C.len⟩ ⟨base, size⟩) (ho : Outside base 0 size s.mem t.mem) :
    WP isa (.block (loadBytes c.C.len c.n (c.sl i) .ebx)) t fun t' =>
      wordsVal t'.mem base (c.sl i) c.n = ofBytes (Spec.Ecdsa.bytesAt s.mem (p.setWidth 64) c.C.len) ∧
      Keeps [.eax] t t' ∧ Outside base (c.sl i) (8 * c.n) t.mem t'.mem := by
  have hl := sl_le c hc.n10 hi
  have h7 := hc.n10
  have := hc.len_hi
  have := hc.len8
  have hsub : Region.Sub ⟨base + BitVec.ofNat 64 (c.sl i), 8 * c.n⟩ ⟨base, size⟩ := Offset.sub_base base hl
  refine WP.mono (loadBytes_ok hs (by decide) hl (by rw [hp]; exact hfit) (by omega) hc.len_hi (by rw [hp]; exact hin)
    (by rw [hp]; exact hd.sub_right hsub)) fun t' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  have hb : Spec.Ecdsa.bytesAt t.mem (p.setWidth 64) c.C.len = Spec.Ecdsa.bytesAt s.mem (p.setWidth 64) c.C.len :=
    List.map_congr_left fun j hj =>
      keep_of_disjoint' ho hd (by decide) (List.mem_range.mp hj) (by omega)
  rw [e, hp, hb]

/-! ## The hash's shift -/

/-- The shift of slot `hs`, if any, by the bits of a hash that are not
`e`'s: only the slots of `k`, `d` and the hash change. -/
theorem setupShift_ok {c : Cfg} (hc : CfgOk c) {hs : Option Nat} (hhs : ShiftOk hs) {t : State}
    {base : Addr} (hs' : Scr t base size) :
    WP isa (.block (c.shiftCode hs)) t fun t' =>
      wordsVal t'.mem base (c.sl K) c.n = wordsVal t.mem base (c.sl K) c.n >>> shAt c hs K ∧
      wordsVal t'.mem base (c.sl D) c.n = wordsVal t.mem base (c.sl D) c.n >>> shAt c hs D ∧
      wordsVal t'.mem base (c.sl E) c.n = wordsVal t.mem base (c.sl E) c.n >>> shAt c hs E ∧
      Keeps [.eax, .edx] t t' ∧ Outside base (c.sl K) (24 * c.n) t.mem t'.mem := by
  have hn := hs'.nowrap
  have h7 := hc.n10
  have hKl := sl_le c h7 (i := K) (by decide)
  have hEl := sl_le c h7 (i := E) (by decide)
  have hKD : c.sl D = c.sl K + 8 * c.n := by rw [sl_eq, sl_eq]; show _ = _ + 8 * c.n; simp only [D, K]; omega
  have hKE : c.sl E = c.sl K + 16 * c.n := by rw [sl_eq, sl_eq]; show _ = _ + 16 * c.n; simp only [E, K]; omega
  have nil : WP isa (.block ([] : List Instr)) t fun t' =>
      wordsVal t'.mem base (c.sl K) c.n = wordsVal t.mem base (c.sl K) c.n >>> 0 ∧
      wordsVal t'.mem base (c.sl D) c.n = wordsVal t.mem base (c.sl D) c.n >>> 0 ∧
      wordsVal t'.mem base (c.sl E) c.n = wordsVal t.mem base (c.sl E) c.n >>> 0 ∧
      Keeps [.eax, .edx] t t' ∧ Outside base (c.sl K) (24 * c.n) t.mem t'.mem :=
    WP.block_nil ⟨Nat.shiftRight_zero.symm, Nat.shiftRight_zero.symm, Nat.shiftRight_zero.symm,
      Keeps.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _⟩
  rcases hhs with rfl | rfl | rfl
  · exact nil
  · by_cases h0 : c.sh = 0
    · simp only [Cfg.shiftCode, h0, ite_true]
      rw [shAt_self, h0, shAt_K_D, shAt_K_E]; exact nil
    · simp only [Cfg.shiftCode, h0, ite_false]
      refine WP.mono (shrWords_ok hs' hKl (by omega) hc.sh) fun t' ⟨e, k, O⟩ =>
        ⟨?_, ?_, ?_, k, O.mono (Nat.le_refl _) (by omega)⟩
      · rw [shAt_self]; exact e
      · rw [shAt_K_D, Nat.shiftRight_zero]; exact O.wordsVal (by omega) (by omega)
      · rw [shAt_K_E, Nat.shiftRight_zero]; exact O.wordsVal (by omega) (by omega)
  · by_cases h0 : c.sh = 0
    · simp only [Cfg.shiftCode, h0, ite_true]
      rw [shAt_self, h0, shAt_E_D, shAt_E_K]; exact nil
    · simp only [Cfg.shiftCode, h0, ite_false]
      refine WP.mono (shrWords_ok hs' hEl (by omega) hc.sh) fun t' ⟨e, k, O⟩ =>
        ⟨?_, ?_, ?_, k, O.mono (by omega) (by omega)⟩
      · rw [shAt_E_K, Nat.shiftRight_zero]; exact O.wordsVal (by omega) (by omega)
      · rw [shAt_E_D, Nat.shiftRight_zero]; exact O.wordsVal (by omega) (by omega)
      · rw [shAt_self]; exact e

/-! ## The constants -/

/-- The constants of `l`, apart slots below `17`, each in its slot; only their
slots change. -/
theorem setupConsts_ok {c : Cfg} (hc : CfgOk c) {base : Addr} : ∀ (l : List (Nat × Nat)) {t : State},
    Scr t base size → (∀ ix ∈ l, ix.1 < 17 ∧ ix.2 < 2 ^ (64 * c.n)) → (l.map Prod.fst).Nodup →
    WP isa (.block (l.flatMap (fun (i, x) => setConst c.n (c.sl i) x))) t fun t' =>
      (∀ ix ∈ l, wordsVal t'.mem base (c.sl ix.1) c.n = ix.2) ∧ Keeps [.eax] t t' ∧
      Unch base (l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem
  | [], _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, Keeps.refl _ _,
      Unch.refl _ _ _⟩
  | (i, x) :: l, t, hs, hb, hnd => by
    rw [List.flatMap_cons]
    have hi := hb (i, x) List.mem_cons_self
    have hl := sl_le c hc.n10 (i := i) (by omega)
    refine WP.block_append (WP.mono (setConst_ok hs hl hi.2) fun t₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    rw [List.map_cons, List.nodup_cons] at hnd
    refine WP.mono (setupConsts_ok hc l hs₁ (fun ix h => hb ix (List.mem_cons_of_mem _ h)) hnd.2)
      fun t' ⟨e', k', U'⟩ => ⟨fun ix h => ?_, k₁.trans k',
        show Unch base ([(c.sl i, 8 * c.n)] ++ l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem from
          O₁.unch.trans U'⟩
    rcases List.mem_cons.mp h with rfl | h
    · refine (U'.wordsVal (fun w hw => ?_) (by have := hs.nowrap; dsimp only; omega)).trans e₁
      obtain ⟨jy, hjy, rfl⟩ := List.mem_map.mp hw
      exact sl_apart c fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hjy)
    · exact e' ix h

theorem consts_fst (c : Cfg) :
    c.consts.map Prod.fst = [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := rfl

theorem consts_nodup (c : Cfg) : (c.consts.map Prod.fst).Nodup := by
  rw [consts_fst]; decide

theorem consts_bounds {c : Cfg} (hc : CfgOk c) :
    ∀ ix ∈ c.consts, ix.1 < 17 ∧ ix.2 < 2 ^ (64 * c.n) := by
  intro ix h
  refine ⟨?_, ?_⟩
  · have := List.mem_map_of_mem (f := Prod.fst) h
    rw [consts_fst] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  · have hp0 : 0 < c.C.p := by have := hc.p_ge; omega
    have hn0 : 0 < c.C.n := by have := hc.n_ge; omega
    have hR : 1 < 2 ^ (64 * c.n) := Nat.one_lt_two_pow (by have := hc.n0; omega)
    have hm : ∀ x, c.mont x < 2 ^ (64 * c.n) := fun x =>
      Nat.lt_trans (Nat.mod_lt (x * c.R) hp0) hc.p_lt
    have hn : ∀ x, x % c.C.n < 2 ^ (64 * c.n) := fun x => Nat.lt_trans (Nat.mod_lt x hn0) hc.n_lt
    have hp2 : c.C.p - 2 < 2 ^ (64 * c.n) := by have := hc.p_lt; omega
    have hn2 : c.C.n - 2 < 2 ^ (64 * c.n) := by have := hc.n_lt; omega
    simp only [Cfg.consts, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact hc.p_lt
    · exact hc.n_lt
    · exact Nat.lt_trans Nat.one_pos hR
    · exact hR
    · exact hm 1
    · exact hm _
    · exact hm _
    · exact hm _
    · exact hm _
    · exact hn _
    · exact hn _
    · exact hp2
    · exact hn2
    · exact Nat.lt_trans Nat.one_pos hR
    · exact hm 1
    · exact Nat.lt_trans Nat.one_pos hR

/-! ## The whole setup -/

theorem setup_eq (c : Cfg) (A : Args) : c.setupWith A =
    .mov .eax (.mem (Cfg.argOp A.sc)) :: (Cfg.saveCode ++
    (.mov .edi (.reg .eax) :: .mov .ebx (.mem (Cfg.argOp A.k)) :: (loadBytes c.C.len c.n (c.sl K) .ebx ++
    (.mov .ebx (.mem (Cfg.argOp A.d)) :: (loadBytes c.C.len c.n (c.sl D) .ebx ++
    (.mov .ebx (.mem (Cfg.argOp A.e)) :: (loadBytes c.C.len c.n (c.sl E) .ebx ++ (c.shiftCode A.hs ++
    (c.consts.flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
    ([.mov .eax (.imm (BitVec.allOnes 32)), .store (sc (c.sl FLAG)) .eax] : List Instr)))))))))) := by
  simp only [Cfg.setupWith, List.append_assoc, List.cons_append, List.nil_append]

theorem setup_ok {c : Cfg} (hc : CfgOk c) {A : Args} {s : State} (hp : SetupPre c A s) :
    WP isa (.block (c.setupWith A)) s (SetupPost c A s (ptr s A.sc)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hsz : size = 8192 := rfl
  have hfit := hp.sc_fit
  have hbn : (ptr s A.sc).toNat = (arg s A.sc).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hw := hp.wr
  have mem : ∀ {i}, i = A.sc ∨ i = A.k ∨ i = A.d ∨ i = A.e → i ∈ A.idx := fun h => by
    simp only [Args.idx, List.mem_cons, List.not_mem_nil, or_false]; exact h
  rw [setup_eq]
  -- The working space's base, and the saves.
  refine wp_movS (hp.argLoad rfl rfl (VG.Proof.Mont.Outside.refl _ _ _ _) (i := A.sc) (mem (.inl rfl)))
    fun s₁ u₁ _ => ?_
  refine WP.block_append (WP.mono (setupSaves_ok (base := ptr s A.sc) (by rw [u₁.gpr]) (by rw [u₁.gpr]; omega)
    (by rw [u₁.wr]; exact hw)) fun s₂ ⟨g₂, rd₂, wr₂, O₂, sv₂⟩ => ?_)
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  have hs₃ : Scr s₃ (ptr s A.sc) size := ⟨by rw [u₃.gpr, g₂, u₁.gpr], by rw [u₃.wr, wr₂, u₁.wr]; exact hw,
    by rw [hbn]; exact hfit⟩
  have RW₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
  have esp₃ : s₃.gpr .esp = s.gpr .esp := by
    rw [u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  have O₃ : Outside (ptr s A.sc) 0 size s.mem s₃.mem := by
    rw [u₃.mem, ← u₁.mem]; exact O₂.mono (Nat.le_refl _) (by omega)
  -- `k`
  refine wp_movS (hp.argLoad esp₃ RW₃ O₃ (i := A.k) (mem (.inr (.inl rfl)))) fun s₄ u₄ _ => ?_
  have hs₄ := hs₃.of_keeps u₄.keeps (by decide)
  refine WP.block_append (WP.mono (setupLoad_ok hc (s := s) hs₄ (i := K) (by decide) u₄.gpr hp.k_fit
    (by rw [u₄.rd, u₄.wr, RW₃]; exact hp.k_in) hp.k_sc (by rw [u₄.mem]; exact O₃))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  rw [u₄.mem] at O₅
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have O₅' : Outside (ptr s A.sc) 0 size s.mem s₅.mem := by
    exact O₃.trans (O₅.mono (Nat.zero_le _) (by have := sl_le c h7 (i := K) (by decide); omega))
  -- `d`
  refine wp_movS (hp.argLoad (by rw [k₅.1 _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [k₅.2.1, k₅.2.2, u₄.rd, u₄.wr, RW₃]) O₅' (i := A.d) (mem (.inr (.inr (.inl rfl))))) fun s₆ u₆ _ => ?_
  have hs₆ := hs₅.of_keeps u₆.keeps (by decide)
  refine WP.block_append (WP.mono (setupLoad_ok hc (s := s) hs₆ (i := D) (by decide) u₆.gpr hp.d_fit
    (by rw [u₆.rd, u₆.wr, k₅.2.1, k₅.2.2, u₄.rd, u₄.wr, RW₃]; exact hp.d_in) hp.d_sc
    (by rw [u₆.mem]; exact O₅')) fun s₇ ⟨e₇, k₇, O₇⟩ => ?_)
  rw [u₆.mem] at O₇
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  have O₇' : Outside (ptr s A.sc) 0 size s.mem s₇.mem := by
    exact O₅'.trans (O₇.mono (Nat.zero_le _) (by have := sl_le c h7 (i := D) (by decide); omega))
  -- the hash
  refine wp_movS (hp.argLoad (by rw [k₇.1 _ (by decide), u₆.other _ (by decide), k₅.1 _ (by decide),
      u₄.other _ (by decide), esp₃])
    (by rw [k₇.2.1, k₇.2.2, u₆.rd, u₆.wr, k₅.2.1, k₅.2.2, u₄.rd, u₄.wr, RW₃]) O₇' (i := A.e) (mem (.inr (.inr (.inr rfl)))))
    fun s₈ u₈ _ => ?_
  have hs₈ := hs₇.of_keeps u₈.keeps (by decide)
  refine WP.block_append (WP.mono (setupLoad_ok hc (s := s) hs₈ (i := E) (by decide) u₈.gpr hp.e_fit
    (by rw [u₈.rd, u₈.wr, k₇.2.1, k₇.2.2, u₆.rd, u₆.wr, k₅.2.1, k₅.2.2, u₄.rd, u₄.wr, RW₃]; exact hp.e_in)
    hp.e_sc (by rw [u₈.mem]; exact O₇')) fun s₉ ⟨e₉, k₉, O₉⟩ => ?_)
  rw [u₈.mem] at O₉
  have hs₉ := hs₈.of_keeps k₉ (by decide)
  -- the shift
  refine WP.block_append (WP.mono (setupShift_ok hc hp.shift hs₉) fun sS ⟨fK, fD, fE, kS, OS⟩ => ?_)
  have hsS := hs₉.of_keeps kS (by decide)
  -- the constants
  refine WP.block_append (WP.mono (setupConsts_ok hc c.consts hsS (consts_bounds hc) (consts_nodup c))
    fun s₁₀ ⟨e₁₀, k₁₀, U₁₀⟩ => ?_)
  have hs₁₀ := hsS.of_keeps k₁₀ (by decide)
  have hsl0 : c.sl 0 = 64 := by rw [sl_eq]; omega
  have O₁₀ : Outside (ptr s A.sc) (c.sl 0) (8 * c.n * 17) sS.mem s₁₀.mem := U₁₀.outside fun w hw => by
    obtain ⟨ix, hix, rfl⟩ := List.mem_map.mp hw
    have := sl_lt c (consts_bounds hc ix hix).1
    have : c.sl 0 ≤ c.sl ix.1 := by rw [hsl0, sl_eq]; omega
    exact ⟨this, by rw [sl_eq c 17] at *; omega⟩
  -- the flag
  refine wp_movS rfl fun s₁₁ u₁₁ _ => ?_
  have hs₁₁ := hs₁₀.of_keeps u₁₁.keeps (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine wp_storeS (hs₁₁.ea (d := c.sl FLAG) (by omega)) (hs₁₁.write (d := c.sl FLAG) (n := 4) (by omega))
    fun s' m' => WP.block_nil ?_
  have O' : Outside (ptr s A.sc) (c.sl FLAG) 4 s₁₀.mem s'.mem := by
    rw [m'.mem, u₁₁.mem]; exact writeW32_outside _ _ _ (by omega)
  -- Everything after the saves writes only in `[64, size)`.
  have h17 := sl_le c h7 (i := 17) (by decide)
  have hK := sl_le c h7 (i := K) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hK17 := sl_lt c (i := 17) (j := K) (by decide)
  have hDK := sl_lt c (i := K) (j := D) (by decide)
  have hED := sl_lt c (i := D) (j := E) (by decide)
  have hFE := sl_lt c (i := E) (j := FLAG) (by decide)
  have h0 : c.sl 0 + 8 * c.n * 17 = c.sl 17 := by rw [sl_eq, sl_eq]; omega
  have Ol : Outside (ptr s A.sc) 64 (size - 64) s₃.mem s'.mem := by
    exact (((((O₅.mono (by omega) (by omega)).trans (O₇.mono (by omega) (by omega))).trans
      (O₉.mono (by omega) (by omega))).trans (OS.mono (by omega) (by omega))).trans
      (O₁₀.mono (by omega) (by omega))).trans (O'.mono (by omega) (by omega))
  have K' : Keeps [.eax, .ebx, .edx, .edi] s s' :=
    (((((((((((u₁.keeps.mono (rs' := [.eax, .ebx, .edx, .edi]) (by decide)).widen
      (⟨fun r _ => by rw [g₂], rd₂, wr₂⟩ : Keeps [] s₁ s₂)).widen u₃.keeps).widen
      u₄.keeps).widen k₅).widen u₆.keeps).widen k₇).widen u₈.keeps).widen k₉).widen kS).widen k₁₀).widen
      (u₁₁.keeps.trans (m'.keeps _))
  refine ⟨hs₁₁.of_keeps (m'.keeps []) (by decide), K', ?_, fun rd hrd => ?_, ?_, ?_, ?_, fun ix hix => ?_, ?_⟩
  · exact (O₃.trans (Ol.mono (Nat.zero_le _) (by omega))).unch
  · have hlt : rd.2 + 4 ≤ 16 := by revert rd; decide
    have hne : rd.1 ≠ .eax := by revert rd; decide
    have hw32 := Ol.w32 (d := rd.2) (by omega) (by omega)
    rw [BitVec.eq_of_toNat_eq hw32, u₃.mem, sv₂ rd hrd, u₁.other _ hne]
  · show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega) (by omega),
      O₁₀.wordsVal (by omega) (by omega), fK, O₉.wordsVal (by omega) (by omega),
      O₇.wordsVal (by omega) (by omega), e₅]
  · show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega) (by omega),
      O₁₀.wordsVal (by omega) (by omega), fD, O₉.wordsVal (by omega) (by omega), e₇]
  · show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega) (by omega),
      O₁₀.wordsVal (by omega) (by omega), fE, e₉]
  · have := sl_lt c (consts_bounds hc ix hix).1
    have := sl_lt c (i := ix.1) (j := FLAG) (by have := (consts_bounds hc ix hix).1; show ix.1 < 44; omega)
    have := sl_le c h7 (i := ix.1) (by have := (consts_bounds hc ix hix).1; omega)
    show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega) (by omega), e₁₀ ix hix]
  · rw [flagW, m'.mem, Mem.readW_writeW_self32, u₁₁.gpr]

end VG.Proof.Ecdsa.X86
