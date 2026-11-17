module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `Ecdsa.X86_64.Lays`, which this module and modules that import it used -/

section

/-!
# ECDSA on x86-64: where the ladder's and the powers' slots are

The slots of `c.ladderCfg`, `c.powP` and `c.powN` are numbered slots `c.sl i`
for distinct `i`, so they are apart as `ladder_ok` and `pow_ok` need
(`ladLay`, `powLayP`, `powLayN`): each fact is one about the numbers `i`,
which `decide` checks.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem sl_mem_map (hn : 0 < c.n) {i : Nat} {l : List Nat} : c.sl i ∈ l.map c.sl ↔ i ∈ l := by
  constructor
  · intro h
    obtain ⟨j, hj, e⟩ := List.mem_map.mp h
    exact sl_inj c hn e ▸ hj
  · exact List.mem_map_of_mem

theorem map_sl_disj (hn : 0 < c.n) {l₁ l₂ : List Nat} (h : ∀ i ∈ l₁, i ∉ l₂) :
    ∀ x ∈ l₁.map c.sl, x ∉ l₂.map c.sl := by
  intro x hx hx'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i hi ((sl_mem_map hn).mp hx')

theorem map_sl_nodup (hn : 0 < c.n) {l : List Nat} (h : l.Nodup) : (l.map c.sl).Nodup :=
  List.Pairwise.map c.sl (fun _ _ hab e => hab (sl_inj c hn e)) h

/-- Numbered slots, apart from the modulus's and the temporary area. -/
theorem lay_map (hc : BaseCfgOk c) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 45 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M size (· ∈ l.map c.sl) := by
  have hn := hc.n0
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn]; exact sl_le c hc.n10 (hl i hi).1
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    rw [hMn]; exact sl_apart c fun h => hxy (h ▸ rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, hmo]; exact sl_apart c (hl i hi).2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, htmp]; exact sl_apart c (hl i hi).2.2

/-- A numbered slot is below the tables, but the temporary area, which for
nine words is between the second and the third, and for six past them all. -/
theorem sl_below_bits (c : Cfg) {i : Nat} (hi : i < 45) (j t : Nat)
    (hT : i ≠ TMP ∨ 2 ≤ j ∧ c.n ≠ 6 := by sl_or) :
    c.sl i + 8 * c.n ≤ bitsAt c.n j + t := by
  rw [bitsAt_eq, sl_eq']
  by_cases h : i = TMP ∧ c.n = 9
  · have hj := (hT.resolve_left fun e => e h.1).1
    have hix : ix c i = 55 := by unfold ix; rw [ite_eq_left h.2, ite_eq_left h.1]
    rw [hix, h.2]
    have := Nat.mul_le_mul_left (64 * 9 + 8) hj
    omega_using [hj]
  · have hix : ix c i = i := by
      by_cases ht : i = TMP
      · have h6 : c.n ≠ 6 := (hT.resolve_left fun e => e ht).2
        have h9 : c.n ≠ 9 := fun e => h ⟨ht, e⟩
        exact ix_of_ne c (.inr fun e => e.elim h9 h6)
      · exact ix_of_ne c (.inl ⟨ht, by omega_using [hi], by omega_using [hi]⟩)
    rw [hix]
    have := Nat.mul_le_mul_left (8 * c.n) hi
    rw [Nat.mul_succ] at this
    omega_using [this]

/-- For six words the temporary area is in slot `83`'s place. -/
theorem sl_tmp6 (c : Cfg) (h6 : c.n = 6) : c.sl TMP = 64 + 8 * c.n * 83 := by
  rw [sl_eq', ix_tmp6 c h6]

/-- A numbered slot is apart from an area past the first two tables, which
for six words ends below the temporary area. -/
theorem sl_apart_hi (c : Cfg) {i : Nat} (hi : i < 45) {a L : Nat} (hlo : bitsAt c.n 2 ≤ a)
    (hhi : c.n = 6 → a + L ≤ c.sl TMP) : c.sl i + 8 * c.n ≤ a ∨ a + L ≤ c.sl i := by
  by_cases h : i = TMP ∧ c.n = 6
  · obtain ⟨rfl, h6⟩ := h
    exact .inr (hhi h6)
  · refine .inl ?_
    have := sl_below_bits c hi 2 0 (by
      by_cases ht : i = TMP
      · exact .inr ⟨by decide, fun e => h ⟨ht, e⟩⟩
      · exact .inl ht)
    omega_using [hlo, this]

/-- The temporary area is apart from the first four tables but the second (the bits of `p - 2`)
for nine words. -/
theorem tmp_apart_bits (c : Cfg) {j : Nat} (hj : j ≠ 1 ∨ c.n ≠ 9) (hj4 : j < 4) (t : Nat) (ht : t ≤ 64 * c.n + 8) :
    c.sl TMP + 8 * c.n ≤ bitsAt c.n j ∨ bitsAt c.n j + t ≤ c.sl TMP := by
  rw [bitsAt_eq, sl_eq']
  by_cases h9 : c.n = 9
  · have hj := hj.resolve_right fun e => e h9
    rw [ix_tmp c h9]
    rw [h9] at ht ⊢
    rcases Nat.lt_or_ge j 1 with h0 | h2
    · right; obtain rfl : j = 0 := by omega_using [h0]
      omega_using [ht]
    · left; have := Nat.mul_le_mul_left (64 * 9 + 8) (show 2 ≤ j by omega_using [hj, h2]); omega_using [hj, h2]
  · by_cases h6 : c.n = 6
    · rw [ix_tmp6 c h6]; right; rw [h6] at ht ⊢
      have := Nat.mul_le_mul_left (64 * 6 + 8) (show j ≤ 3 by omega_using [hj4]); omega_using [hj4, ht]
    · rw [ix_of_ne c (.inr fun e => e.elim h9 h6)]; left; simp only [TMP]
      have := Nat.mul_le_mul_left (64 * c.n + 8) (Nat.zero_le j)
      omega_using []

/-- A numbered slot is apart from the first `t` bytes of table `j`: the
temporary area too, unless the table is the second, for nine words. -/
theorem sl_apart_bits (c : Cfg) {i : Nat} (hi : i < 45) {j : Nat} (hj : i ≠ TMP ∨ j ≠ 1 ∨ c.n ≠ 9) (t : Nat)
    (ht : t ≤ 64 * c.n + 8) (hj4 : j < 4 := by omega) :
    c.sl i + 8 * c.n ≤ bitsAt c.n j ∨ bitsAt c.n j + t ≤ c.sl i := by
  by_cases hT : i = TMP
  · subst hT; exact tmp_apart_bits c (hj.resolve_left fun h => h rfl) hj4 t ht
  · exact .inl (by simpa only [Nat.add_zero] using sl_below_bits c hi j 0 (.inl hT))

theorem rcbApart_of (hn : 0 < c.n) {S : RcbSlots} {p q o : Pt} {lw lr : List Nat}
    (hw : rcbW S o = lw.map c.sl) (hr : rcbR S p q = lr.map c.sl) (hnd : lw.Nodup)
    (hd : ∀ i ∈ lr, i ∉ lw) : RcbApart S p q o :=
  ⟨hw ▸ map_sl_nodup hn hnd, by rw [hw, hr]; exact map_sl_disj hn hd⟩

theorem ladLay (hc : BaseCfgOk c) : LadLay c.ladderCfg size := by
  have hn := hc.n0
  have h7 := hc.n10
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, B3P, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, B3P, DX, DY, DZ, GX, GY, ONEP]) rfl rfl (by decide) (by decide), ?_,
    ⟨fun h => by have := sl_inj c hn (i := RX) (j := RY) h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn (i := RX) (j := RZ) h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn (i := RY) (j := RZ) h; exact absurd this (by decide)⟩, ?_,
    ⟨show 1 ≤ 64 * c.n by omega_using [hn], show 64 * c.n < 2 ^ 16 by omega_using [h7]⟩, bitsAt_le c h7 (by decide), ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, B3P, GX, GY, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5,
      DX, DY, DZ, TX, TY, TZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, B3P, GX, GY, ONEP])
      (l₂ := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (by decide)
  · exact map_sl_disj hn (l₁ := [RX, RY, RZ]) (l₂ := [DX, DY, DZ, TX, TY, TZ]) (by decide)
  · intro w hw
    simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · have hy' : y ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ].map c.sl := hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      have hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ], i < 45 ∧ i ≠ TMP := by decide
      exact Or.inr (sl_below_bits c (hl i hi).1 0 0 (.inl (hl i hi).2))
    · show bitsAt c.n 0 + 64 * c.n ≤ c.sl TMP ∨ c.sl TMP + 8 * c.n ≤ bitsAt c.n 0
      have := tmp_apart_bits c (j := 0) (.inl (by decide)) (by decide) (64 * c.n) (by omega_using []); omega_using [this]

theorem powLay_of (hc : BaseCfgOk c) {jm : Nat} (hjm : jm ∉ [ACC, PT, TMP])
    (minv : BitVec 64) {red : Red} {adx sparse fnN : Bool}
    {base one j : Nat} (hj : j < 3) (hb : base ∉ [ACC, PT, TMP]) (hb45 : base < 45) (ho : one ≠ ACC)
    (ho45 : one < 45) {nb : Nat} (hnb : 1 ≤ nb ∧ nb ≤ 64 * c.n) (hjT : j ≠ 1 ∨ c.n ≠ 9) :
    PowLay ⟨⟨c.n, c.sl jm, c.sl TMP, minv, red, false, adx, sparse, false, fnN, none⟩, c.sl ACC, c.sl PT, c.sl base, c.sl one, bitsAt c.n j,
      nb⟩ size := by
  have hn := hc.n0
  have h7 := hc.n10
  have hw : ∀ i, i ∉ [ACC, PT, TMP] →
      ∀ w ∈ powW ⟨⟨c.n, c.sl jm, c.sl TMP, minv, red, false, adx, sparse, false, fnN, none⟩, c.sl ACC, c.sl PT, c.sl base, c.sl one,
        bitsAt c.n j, nb⟩, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
    intro i hi w hw
    simp only [powW, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rcases hw with rfl | rfl | rfl
    · exact sl_apart c hi.1
    · exact sl_apart c hi.2.1
    · exact sl_apart c hi.2.2
  refine ⟨sl_le c h7 (by decide), sl_le c h7 (by decide), sl_le c h7 hb45, sl_le c h7 ho45,
    Nat.le_trans (Nat.add_le_add_left hnb.2 _) (bitsAt_le c h7 hj), ⟨hnb.1, show nb < 2 ^ 16 by omega_using [hnb, h7]⟩,
    sl_apart c (by decide), sl_apart c (by decide), sl_apart c (by decide), sl_apart c (Ne.symm ho),
    hw base hb, ?_,
    hw jm hjm⟩
  intro w hw'
  simp only [powW, List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with rfl | rfl | rfl
  · exact Or.inr (sl_below_bits c (by decide) j 0)
  · exact Or.inr (sl_below_bits c (by decide) j 0)
  · show bitsAt c.n j + nb ≤ c.sl TMP ∨ c.sl TMP + 8 * c.n ≤ bitsAt c.n j
    have := tmp_apart_bits c hjT (by omega_using [hj]) (64 * c.n) (by omega_using []); omega_using [hnb, this]

/-- The power modulo `p`, which reads the bits of `p - 2` where the
temporary area of nine words is. -/
theorem powLayP (hc : BaseCfgOk c) (h9 : c.n ≠ 9) : PowLay c.powP size :=
  powLay_of hc (jm := MP) (by decide) _ (j := 1) (by decide) (base := RZ) (by decide) (by decide)
    (one := ONEP) (by decide) (by decide) ⟨by have := hc.n0; omega_using [this], Nat.le_refl _⟩ (.inr h9)

/-- `e < 2^(bitLen e k)`, `bitLen e k ≤ k`, and `1 ≤ bitLen e k` for `1 ≤ e < 2^k`. -/
theorem bitLen_ok (e : Nat) : ∀ k, e < 2 ^ k → e < 2 ^ bitLen e k ∧ bitLen e k ≤ k ∧ (1 ≤ e → 1 ≤ bitLen e k)
  | 0, h => ⟨h, Nat.le_refl _, fun h1 => by simp at h; omega⟩
  | k + 1, h => by
    rw [bitLen]
    split
    · rename_i hk
      obtain ⟨a, b, c⟩ := bitLen_ok e k hk
      exact ⟨a, by omega_using [b], c⟩
    · exact ⟨h, Nat.le_refl _, fun _ => by omega_using []⟩

/-- The power mod `n`'s bits: `n - 2 < 2^nbits`, `1 ≤ nbits ≤ 64 n`. -/
theorem nbitsN_ok (hc : BaseCfgOk c) :
    1 ≤ bitLen (c.C.n - 2) (64 * c.n) ∧ bitLen (c.C.n - 2) (64 * c.n) ≤ 64 * c.n ∧
      c.C.n - 2 < 2 ^ bitLen (c.C.n - 2) (64 * c.n) := by
  have hlt : c.C.n - 2 < 2 ^ (64 * c.n) := by have := hc.n_lt; omega_using [this]
  obtain ⟨a, b, d⟩ := bitLen_ok (c.C.n - 2) (64 * c.n) hlt
  exact ⟨d (by have := hc.n_ge; omega_using [this]), b, a⟩

theorem powLayN (hc : BaseCfgOk c) : PowLay c.powN size :=
  powLay_of hc (jm := MN) (by decide) _ (j := 2) (by decide) (base := KM) (by decide) (by decide)
    (one := ONEN) (by decide) (by decide) ⟨(nbitsN_ok hc).1, (nbitsN_ok hc).2.1⟩ (.inl (by decide))

end VG.Proof.Ecdsa.X86_64

end

end

/-! ### `Ecdsa.X86_64.Setup`, which this module and modules that import it used -/

section

/-!
# ECDSA on x86-64: the setup

`Cfg.setup` saves the callee-saved registers at the start of the working
space (`setupSaves_ok`), moves `out` to `r14` and the working space's
base to `rdi` (`setupMovs_ok`), reads `k`, `d` and the hash big-endian into
their slots (`setupLoad_ok`, once each), stores the constants
(`setupConsts_ok`, by induction on the list), sets the flag to all ones and
keeps `out` in `rsi` (`setupOut_ok`): `setup_ok`, the state `SetupPost`
describes.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-! ## Saving the callee-saved registers -/

theorem setupSaved_lt : ∀ rd ∈ Cfg.saved, rd.2 + 8 ≤ 48 := by decide

theorem setupSaves_ok {s : State} {base : Addr} (hb : s.gpr .r8 = base)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) :
    WP isa (.block (Spill.saveCode .r8 Cfg.saved)) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 48 s.mem s'.mem ∧
      Spill.Saved s'.mem base s.gpr Cfg.saved := by
  refine WP.mono (Spill.save_ok .r8 Cfg.saved s fun p hp => ?_) fun s' ⟨hg, hrd, hwr, hm⟩ =>
    ⟨hg, hrd, hwr, ?_, ?_⟩
  · have := setupSaved_lt p hp
    have hsz : size = 8192 := rfl
    rw [hb]; exact ⟨_, hw, Offset.contains_base base (by omega_arith) (by omega_arith)⟩
  · rw [hm, hb]
    intro x hx
    refine Spill.saveMem_frame_base _ _ _ _ setupSaved_lt (by decide) x fun r hr hx' => ?_
    rw [List.mem_singleton.mp hr] at hx'
    simp only [Region.Contains, ofs] at hx hx'
    omega_arith
  · rw [hm, hb]; exact Spill.saveMem_saved _ _ _ _ (by decide)

/-! ## `out` to `r14`, the working space to `rdi` -/

theorem setupMovs_ok (s : State) :
    WP isa (.block ([.mov .r14 (.reg .rdi), .mov .rdi (.reg .r8)] : List Instr)) s fun s' =>
      s'.gpr .r14 = s.gpr .rdi ∧ s'.gpr .rdi = s.gpr .r8 ∧ KeepRegs [.r14, .rdi] s s' ∧
      s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

/-! ## `out` to `rsi` -/

theorem setupOut_ok (s : State) :
    WP isa (.block ([.mov .rsi (.reg .r14)] : List Instr)) s fun s' =>
      s'.gpr .rsi = s.gpr .r14 ∧ KeepRegs [.rsi] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

/-! ## Reading `k`, `d` and the hash -/

/-- The `len` bytes at `p` (readable, outside the working space, and so
unchanged since `s`) to slot `i`. -/
theorem setupLoad_ok {c : Cfg} (hc : BaseCfgOk c) {s t : State} {base p : Addr} {src : Reg} {i : Nat}
    (hs : Scr t base size) (hsrc : src ≠ .rax) (hi : i < 45) (hp : t.gpr src = p)
    (hin : ∀ e, e + 8 ≤ c.C.len → InRegions (t.rd ++ t.wr) (p + BitVec.ofNat 64 e) 8)
    (hd : Region.Disjoint ⟨p, c.C.len⟩ ⟨base, size⟩) (ho : Outside base 0 size s.mem t.mem) :
    WP isa (.block (loadBytes c.C.len c.n (c.sl i) src)) t fun t' =>
      wordsVal t'.mem base (c.sl i) c.n = ofBytes (Spec.Ecdsa.bytesAt s.mem p c.C.len) ∧
      KeepRegs [.rax] t t' ∧ Outside base (c.sl i) (8 * c.n) t.mem t'.mem := by
  obtain hl := sl_le c hc.n10 hi
  have h7 := hc.n10
  have := hc.len8; have := hc.len_lo; have := hc.len_hi
  have hsz : size = 8192 := rfl
  refine WP.mono (loadBytes_ok hs hsrc hl hc.len8 hc.len_lo hc.len_hi (by rw [hp]; exact hin)
    (by rw [hp]; exact hd.sub_right (Offset.sub_base base hl))) fun t' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  obtain hb : Spec.Ecdsa.bytesAt t.mem p c.C.len = Spec.Ecdsa.bytesAt s.mem p c.C.len :=
    List.map_congr_left fun j hj =>
      keep_of_disjoint' ho hd (by decide) (List.mem_range.mp hj) (by omega_arith)
  rw [e, hp, hb]

/-- Which slot `setupWith hs` may shift: none, `d`'s or the hash's. -/
def ShiftOk (hs : Option Nat) : Prop := hs = none ∨ hs = some D ∨ hs = some E

/-- The shift of slot `hs`, if any, by the bits of a hash that are not
`e`'s: only the slots of `d` and the hash change. -/
theorem setupShift_ok {c : Cfg} (hc : BaseCfgOk c) {hs : Option Nat} (hhs : ShiftOk hs) {t : State}
    {base : Addr} (hs' : Scr t base size) :
    WP isa (.block (c.shiftCode hs)) t fun t' =>
      wordsVal t'.mem base (c.sl D) c.n = wordsVal t.mem base (c.sl D) c.n >>> shAt c hs D ∧
      wordsVal t'.mem base (c.sl E) c.n = wordsVal t.mem base (c.sl E) c.n >>> shAt c hs E ∧
      KeepRegs [.rax, .rdx] t t' ∧ Outside base (c.sl D) (16 * c.n) t.mem t'.mem := by
  have hn := hs'.nowrap
  have h7 := hc.n10
  obtain hDl := sl_le c h7 (i := D) (by decide)
  obtain hEl := sl_le c h7 (i := E) (by decide)
  obtain hDE : c.sl E = c.sl D + 8 * c.n := by simp (disch := sl_ne) only [sl_eq]; show _ = _ + 8 * c.n; simp only [D, E]; omega_arith
  obtain nil : WP isa (.block ([] : List Instr)) t fun t' =>
      wordsVal t'.mem base (c.sl D) c.n = wordsVal t.mem base (c.sl D) c.n >>> 0 ∧
      wordsVal t'.mem base (c.sl E) c.n = wordsVal t.mem base (c.sl E) c.n >>> 0 ∧
      KeepRegs [.rax, .rdx] t t' ∧ Outside base (c.sl D) (16 * c.n) t.mem t'.mem :=
    WP.block_nil ⟨Nat.shiftRight_zero.symm, Nat.shiftRight_zero.symm, ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  rcases hhs with rfl | rfl | rfl
  · exact nil
  · by_cases h0 : c.sh = 0
    · simp only [Cfg.shiftCode, h0, ite_true]
      rw [shAt_self, h0, shAt_D_E]; exact nil
    · simp only [Cfg.shiftCode, h0, ite_false]
      refine WP.mono (shrWords_ok hs' hDl (by omega_arith) hc.sh) fun t' ⟨e, k, O⟩ => ⟨?_, ?_, k, O.mono (Nat.le_refl _) (by omega_arith)⟩
      · rw [shAt_self]; exact e
      · rw [shAt_D_E, Nat.shiftRight_zero]; exact O.wordsVal (by omega_arith) (by omega_arith)
  · by_cases h0 : c.sh = 0
    · simp only [Cfg.shiftCode, h0, ite_true]
      rw [shAt_self, h0, shAt_E_D]; exact nil
    · simp only [Cfg.shiftCode, h0, ite_false]
      refine WP.mono (shrWords_ok hs' hEl (by omega_arith) hc.sh) fun t' ⟨e, k, O⟩ =>
        ⟨?_, ?_, k, O.mono (by omega_arith) (by omega_arith)⟩
      · rw [shAt_E_D, Nat.shiftRight_zero]; exact O.wordsVal (by omega_arith) (by omega_arith)
      · rw [shAt_self]; exact e

/-! ## The constants -/

/-- The constants of `l`, apart slots below `17`, each in its slot; only their
slots change. -/
theorem setupConsts_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} : ∀ (l : List (Nat × Nat)) {t : State},
    Scr t base size → (∀ ix ∈ l, ix.1 < 17 ∧ ix.2 < 2 ^ (64 * c.n)) → (l.map Prod.fst).Nodup →
    WP isa (.block (l.flatMap (fun (i, x) => setConst c.n (c.sl i) x))) t fun t' =>
      (∀ ix ∈ l, wordsVal t'.mem base (c.sl ix.1) c.n = ix.2) ∧ KeepRegs [.rax] t t' ∧
      Unch base (l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem
  | [], _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, ⟨fun _ _ => rfl, rfl, rfl⟩,
      Unch.refl _ _ _⟩
  | (i, x) :: l, t, hs, hb, hnd => by
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain hi := hb (i, x) List.mem_cons_self
    obtain hl := sl_le c hc.n10 (i := i) (by omega_arith)
    have hsz : size = 8192 := rfl
    refine WP.mono (setConst_ok hs hl hi.2) fun t₁ ⟨e₁, k₁, O₁⟩ => ?_
    obtain hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [List.map_cons, List.nodup_cons] at hnd
    refine WP.mono (setupConsts_ok hc l hs₁ (fun ix h => hb ix (List.mem_cons_of_mem _ h)) hnd.2)
      fun t' ⟨e', k', U'⟩ => ⟨fun ix h => ?_, k₁.trans k',
        show Unch base ([(c.sl i, 8 * c.n)] ++ l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem from
          O₁.unch.trans U'⟩
    rcases List.mem_cons.mp h with rfl | h
    · refine (U'.wordsVal (fun w hw => ?_) (by dsimp only; omega_arith)).trans e₁
      obtain ⟨jy, hjy, rfl⟩ := List.mem_map.mp hw
      exact sl_apart c fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hjy)
    · exact e' ix h

theorem consts_fst (c : Cfg) :
    c.consts.map Prod.fst = [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := rfl

theorem consts_nodup (c : Cfg) : (c.consts.map Prod.fst).Nodup := by
  rw [consts_fst]; decide

theorem consts_ne_tmp (c : Cfg) : ∀ ix ∈ c.consts, ix.1 ≠ TMP := by
  intro ix hix
  have : ix.1 ∈ c.consts.map Prod.fst := List.mem_map_of_mem hix
  rw [consts_fst] at this
  revert this; generalize ix.1 = i; decide +revert

theorem consts_bounds {c : Cfg} (hc : BaseCfgOk c) :
    ∀ ix ∈ c.consts, ix.1 < 17 ∧ ix.2 < 2 ^ (64 * c.n) := by
  intro ix h
  refine ⟨?_, ?_⟩
  · have := List.mem_map_of_mem (f := Prod.fst) h
    rw [consts_fst] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega_arith
  · have hp0 : 0 < c.C.p := by have := hc.p_ge; omega_arith
    obtain hn0 : 0 < c.C.n := by have := hc.n_ge; omega_arith
    obtain hR : 1 < 2 ^ (64 * c.n) := Nat.one_lt_two_pow (by have := hc.n0; omega_arith)
    obtain hm : ∀ x, c.mont x < 2 ^ (64 * c.n) := fun x =>
      Nat.lt_trans (Nat.mod_lt (x * c.R) hp0) hc.p_lt
    obtain hn : ∀ x, x % c.C.n < 2 ^ (64 * c.n) := fun x => Nat.lt_trans (Nat.mod_lt x hn0) hc.n_lt
    obtain hp2 : c.C.p - 2 < 2 ^ (64 * c.n) := by have := hc.p_lt; omega_arith
    obtain hn2 : c.C.n - 2 < 2 ^ (64 * c.n) := by have := hc.n_lt; omega_arith
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

/-! ## The flag -/

theorem setupFlag_ok {c : Cfg} (hc : BaseCfgOk c) {t : State} {base : Addr} (hs : Scr t base size) :
    WP isa (.block (setConst 1 (c.sl FLAG) (2 ^ 64 - 1))) t fun t' =>
      word t'.mem base (c.sl FLAG) = BitVec.allOnes 64 ∧ KeepRegs [.rax] t t' ∧
      Outside base (c.sl FLAG) (8 * 1) t.mem t'.mem := by
  obtain hl := sl_le c hc.n10 (i := FLAG) (by decide)
  have := hc.n0
  refine WP.mono (setConst_ok hs (by omega_arith) (by decide)) fun t' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  obtain e' : (word t'.mem base (c.sl FLAG)).toNat = 2 ^ 64 - 1 := by
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at e
    exact e
  exact BitVec.eq_of_toNat_eq (by rw [e', BitVec.toNat_allOnes])

/-! ## The whole setup -/

theorem setup_eq (c : Cfg) (hs : Option Nat) : c.setupWith hs = Spill.saveCode .r8 Cfg.saved ++
    (([.mov .r14 (.reg .rdi), .mov .rdi (.reg .r8)] : List Instr) ++
    (loadBytes c.C.len c.n (c.sl K) .rcx ++ (loadBytes c.C.len c.n (c.sl D) .rsi ++
    (loadBytes c.C.len c.n (c.sl E) .rdx ++ (c.shiftCode hs ++
    (c.consts.flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
    (setConst 1 (c.sl FLAG) (2 ^ 64 - 1) ++ ([.mov .rsi (.reg .r14)] : List Instr)))))))) := by
  simp only [Cfg.setupWith, List.append_assoc]; rfl

theorem setup_ok {c : Cfg} (hc : BaseCfgOk c) {hs : Option Nat} (hhs : ShiftOk hs) {s : State}
    (hp : SetupPre c s) : WP isa (.block (c.setupWith hs)) s (SetupPost c hs s (s.gpr .r8)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hsz : size = 8192 := rfl
  have hw : (⟨s.gpr .r8, size⟩ : Region) ∈ s.wr := hp.wr
  rw [setup_eq c hs, WP.block_append_iff]
  refine WP.mono (setupSaves_ok rfl hw) fun s₁ ⟨g₁, rd₁, wr₁, O₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setupMovs_ok s₁) fun s₂ ⟨r14₂, rdi₂, k₂, m₂⟩ => ?_
  obtain hs₂ : Scr s₂ (s.gpr .r8) size :=
    ⟨by rw [rdi₂, g₁], by rw [k₂.wr, wr₁]; exact hw, hp.sc_fit⟩
  obtain G₂ : ∀ r, r ≠ .r14 → r ≠ .rdi → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [k₂.gpr r (by simp [h₁, h₂]), g₁]
  obtain RD₂ : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [k₂.rd, k₂.wr, rd₁, wr₁]
  obtain O₂ : Outside (s.gpr .r8) 0 size s.mem s₂.mem := by
    rw [m₂]; exact O₁.mono (Nat.le_refl _) (by omega_arith)
  obtain hK : c.sl K = 64 + 8 * c.n * 31 := sl_eq c K
  obtain hD : c.sl D = 64 + 8 * c.n * 32 := sl_eq c D
  obtain hE : c.sl E = 64 + 8 * c.n * 33 := sl_eq c E
  obtain hF : c.sl FLAG = 64 + 8 * c.n * 44 := sl_eq c FLAG
  obtain h17 : c.sl 17 = 64 + 8 * c.n * 17 := sl_eq c 17
  -- `k`
  rw [WP.block_append_iff]
  refine WP.mono (setupLoad_ok hc (s := s) hs₂ (by decide) (i := K) (by decide)
    (G₂ _ (by decide) (by decide)) (by rw [RD₂]; exact hp.k_in) hp.k_sc O₂)
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  -- `d`
  rw [WP.block_append_iff]
  refine WP.mono (setupLoad_ok hc (s := s) hs₃ (by decide) (i := D) (by decide)
    (by rw [k₃.gpr _ (by decide)]; exact G₂ _ (by decide) (by decide))
    (by rw [k₃.rd, k₃.wr, RD₂]; exact hp.d_in) hp.d_sc
    (O₂.trans (O₃.mono (Nat.zero_le _) (by omega_arith)))) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  -- the hash
  rw [WP.block_append_iff]
  refine WP.mono (setupLoad_ok hc (s := s) hs₄ (by decide) (i := E) (by decide)
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide)]; exact G₂ _ (by decide) (by decide))
    (by rw [k₄.rd, k₄.wr, k₃.rd, k₃.wr, RD₂]; exact hp.digest_in) hp.digest_sc
    ((O₂.trans (O₃.mono (Nat.zero_le _) (by omega_arith))).trans (O₄.mono (Nat.zero_le _) (by omega_arith))))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  obtain hs₅ := hs₄.of_keepRegs k₅ (by decide)
  -- `e`, the hash shifted
  rw [WP.block_append_iff]
  refine WP.mono (setupShift_ok hc hhs hs₅) fun s₅' ⟨eSD, eS, kS, OS⟩ => ?_
  obtain hs₅' := hs₅.of_keepRegs kS (by decide)
  -- the constants
  rw [WP.block_append_iff]
  refine WP.mono (setupConsts_ok hc c.consts hs₅' (consts_bounds hc) (consts_nodup c))
    fun s₆ ⟨e₆, k₆, U₆⟩ => ?_
  obtain hs₆ := hs₅'.of_keepRegs k₆ (by decide)
  obtain O₆ : Outside (s.gpr .r8) (c.sl 0) (8 * c.n * 17) s₅'.mem s₆.mem := U₆.outside fun w hw => by
    obtain ⟨ix, hix, rfl⟩ := List.mem_map.mp hw
    have := sl_lt c (consts_bounds hc ix hix).1 (.inl (consts_ne_tmp c ix hix))
    obtain h0' : c.sl 0 = 64 := by simp (disch := sl_ne) only [sl_eq]; omega_arith
    have : c.sl 0 ≤ c.sl ix.1 := by
      rw [h0', sl_eq c ix.1 ⟨consts_ne_tmp c ix hix, by have := (consts_bounds hc ix hix).1; omega_arith⟩]; omega_arith
    exact ⟨this, by omega_arith⟩
  obtain hsl0 : c.sl 0 = 64 := by simp (disch := sl_ne) only [sl_eq]; omega_arith
  -- the flag
  rw [WP.block_append_iff]
  refine WP.mono (setupFlag_ok hc hs₆) fun s₇ ⟨f₇, k₇, O'⟩ => ?_
  -- `out` to `rsi`
  refine WP.mono (setupOut_ok s₇) fun s' ⟨rsi', k', m'⟩ => ?_
  obtain K₃ : KeepRegs [.rax, .rdx] s₂ s₇ :=
    ((((((k₃.trans k₄).trans k₅).mono (by decide)).trans kS).trans (k₆.mono (by decide))).trans
      (k₇.mono (by decide)))
  obtain hs₇ := hs₆.of_keepRegs k₇ (by decide)
  -- Everything after the movs writes only in `[64, size)`.
  obtain Ol : Outside (s.gpr .r8) 64 (size - 64) s₂.mem s₇.mem :=
    (((((O₃.mono (by omega_arith) (by omega_arith)).trans (O₄.mono (by omega_arith) (by omega_arith))).trans
      (O₅.mono (by omega_arith) (by omega_arith))).trans (OS.mono (by omega_arith) (by omega_arith))).trans
      (O₆.mono (by omega_arith) (by omega_arith))).trans (O'.mono (by omega_arith) (by omega_arith))
  refine ⟨hs₇.of_keepRegs k' (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun ix hix => ?_, ?_⟩
  · rw [rsi', K₃.gpr _ (by decide), r14₂, g₁]
  · refine ⟨fun r hr => ?_, by rw [k'.rd, K₃.rd, k₂.rd, rd₁], by rw [k'.wr, K₃.wr, k₂.wr, wr₁]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k'.gpr r (by simp [hr.2.2.2.1]), K₃.gpr r (by simp [hr.1, hr.2.2.2.2]), G₂ r hr.2.2.1 hr.2.1]
  · rw [m']; exact (O₂.trans (Ol.mono (Nat.zero_le _) (by omega_arith))).unch
  · intro rd hrd
    have := setupSaved_lt rd hrd
    rw [m']
    exact (Ol.word (d := rd.2) (by omega_arith) (by omega_arith)).trans
      ((congrArg (fun m => Mem.readW m _ 64) m₂).trans (sv₁ rd hrd))
  · show wordsVal s'.mem _ _ _ = _
    rw [m', O'.wordsVal (by omega_arith) (by omega_arith), O₆.wordsVal (by omega_arith) (by omega_arith),
      OS.wordsVal (by omega_arith) (by omega_arith), O₅.wordsVal (by omega_arith) (by omega_arith),
      O₄.wordsVal (by omega_arith) (by omega_arith), e₃]
  · show wordsVal s'.mem _ _ _ = _
    rw [m', O'.wordsVal (by omega_arith) (by omega_arith), O₆.wordsVal (by omega_arith) (by omega_arith),
      eSD, O₅.wordsVal (by omega_arith) (by omega_arith), e₄]
  · show wordsVal s'.mem _ _ _ = _
    rw [m', O'.wordsVal (by omega_arith) (by omega_arith), O₆.wordsVal (by omega_arith) (by omega_arith), eS, e₅]
  · have := sl_lt c (consts_bounds hc ix hix).1 (.inl (consts_ne_tmp c ix hix))
    have := sl_le c hc.n10 (i := 17) (by decide)
    show wordsVal s'.mem _ _ _ = _
    rw [m', O'.wordsVal (by omega_arith) (by omega_arith), e₆ ix hix]
  · rw [m']; exact f₇

end VG.Proof.Ecdsa.X86_64

end

end

/-!
# ECDSA on x86-64: what every phase keeps

After `setup`, the slots below `12` but the temporary area's hold constants
the code only reads, and `[0, 48)` the saved registers (`Fixed`); every
later phase writes only slots from `12` on, the temporary area, the flag
and the tables (`FixedOk`), so it keeps them (`Fixed.unch`). A slot or a
table byte apart from what a phase writes keeps its value too (`sv_unch`,
`tbl_unch`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- The constants and the saved registers `g`. -/
structure Fixed (c : Cfg) (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop where
  mp : wordsVal m base (c.sl MP) c.n = c.C.p
  mn : wordsVal m base (c.sl MN) c.n = c.C.n
  zero : wordsVal m base (c.sl ZERO) c.n = 0
  one : wordsVal m base (c.sl ONE) c.n = 1
  onep : wordsVal m base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p
  ap : wordsVal m base (c.sl AP) c.n = c.mont c.C.a
  b3p : wordsVal m base (c.sl B3P) c.n = c.mont (3 * c.C.b)
  gx : wordsVal m base (c.sl GX) c.n = c.mont c.C.gx
  gy : wordsVal m base (c.sl GY) c.n = c.mont c.C.gy
  r2n : wordsVal m base (c.sl R2N) c.n = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n
  onen : wordsVal m base (c.sl ONEN) c.n = 2 ^ (64 * c.n) % c.C.n
  saved : Spill.Saved m base g Cfg.saved

/-- What a phase writes misses the constants and the saved registers. -/
def FixedOk (c : Cfg) (W : List (Nat × Nat)) : Prop :=
  ∀ w ∈ W, (w.1 = c.sl TMP ∧ w.2 = 8 * c.n) ∨ c.sl 12 ≤ w.1

/-- The ranges of numbered slots. -/
abbrev slW (c : Cfg) (l : List Nat) : List (Nat × Nat) := l.map fun i => (c.sl i, 8 * c.n)

theorem FixedOk.append {W W' : List (Nat × Nat)} (h : FixedOk c W) (h' : FixedOk c W') :
    FixedOk c (W ++ W') := fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

theorem fixedOk_slW {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) (h55 : 55 ∉ l := by decide)
    (h83 : 83 ∉ l := by decide) :
    FixedOk c (slW c l) := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  rcases hl i hi with h | h
  · exact Or.inl ⟨by rw [h], rfl⟩
  · refine Or.inr ?_
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [h]
    · exact Nat.le_trans (Nat.le_add_right _ _) (sl_lt c h (.inl (by decide)) ⟨fun e => h55 (e ▸ hi), fun e => h83 (e ▸ hi)⟩)

theorem fixedOk_tbl (j : Nat) : FixedOk c [(bitsAt c.n j, 64 * c.n)] := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (by decide) j 0))

theorem fixedOk_flag : FixedOk c [(c.sl FLAG, 8)] := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide)))

/-- A constant's slot is apart from what a phase writes. -/
theorem fixed_apart {W : List (Nat × Nat)} (hW : FixedOk c W) {i : Nat} (hi : i < 12) (hit : i ≠ TMP) :
    ∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rcases hW w hw with ⟨h1, h2⟩ | h
  · rw [h1, h2]; exact sl_apart c hit
  · exact Or.inl (Nat.le_trans (sl_lt c hi) h)

theorem Fixed.unch {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Fixed c base g m)
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {W : List (Nat × Nat)} (hW : FixedOk c W)
    (hu : Unch base W m m') : Fixed c base g m' := by
  have e : ∀ i, i < 12 → i ≠ TMP → wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
    fun i hi hit => hu.wordsVal (fixed_apart hW hi hit) (by have := sl_le c h7 (i := i) (by omega_using [hi]); omega_using [hn, this])
  refine ⟨(e MP (by decide) (by decide)).trans h.mp, (e MN (by decide) (by decide)).trans h.mn,
    (e ZERO (by decide) (by decide)).trans h.zero, (e ONE (by decide) (by decide)).trans h.one,
    (e ONEP (by decide) (by decide)).trans h.onep, (e AP (by decide) (by decide)).trans h.ap,
    (e B3P (by decide) (by decide)).trans h.b3p, (e GX (by decide) (by decide)).trans h.gx,
    (e GY (by decide) (by decide)).trans h.gy, (e R2N (by decide) (by decide)).trans h.r2n,
    (e ONEN (by decide) (by decide)).trans h.onen, fun p hp => ?_⟩
  have := setupSaved_lt p hp
  refine (hu.word (d := p.2) (fun w hw => Or.inl ?_) (by omega_using [this])).trans (h.saved p hp)
  rcases hW w hw with ⟨h1, -⟩ | h
  · rw [h1, sl_eq']; exact Nat.le_trans this (Nat.le_trans (by decide) (Nat.le_add_right 64 _))
  · simp (disch := sl_ne) only [sl_eq] at h; omega_using [this, h]

/-- A slot apart from the ranges of other numbered slots. -/
theorem apart_slW {l : List Nat} {i : Nat} (hi : i ∉ l) :
    ∀ w ∈ slW c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
  exact sl_apart c fun h => hi (h ▸ hj)

theorem apart_tbl {i : Nat} (hi : i < 45) (j : Nat) (hT : i ≠ TMP ∨ 2 ≤ j ∧ c.n ≠ 6 := by sl_or) :
    ∀ w ∈ [(bitsAt c.n j, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (by have := sl_below_bits c hi j 0 hT; omega_using [this])

theorem apart_flag (h0 : 0 < c.n) {i : Nat} (hi : i ≠ FLAG) :
    ∀ w ∈ [(c.sl FLAG, 8)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_apart c hi
  dsimp only
  omega_using [h0, this]

theorem apart_append {W W' : List (Nat × Nat)} {x k : Nat}
    (h : ∀ w ∈ W, x + k ≤ w.1 ∨ w.1 + w.2 ≤ x) (h' : ∀ w ∈ W', x + k ≤ w.1 ∨ w.1 + w.2 ≤ x) :
    ∀ w ∈ W ++ W', x + k ≤ w.1 ∨ w.1 + w.2 ≤ x :=
  fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

/-- A number in a slot apart from what changed. -/
theorem sv_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m')
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {i : Nat} (hi : i < 45)
    (hW : ∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
  hu.wordsVal hW (by have := sl_le c h7 hi; omega_using [hn, this])

/-- A byte of table `j` apart from what changed. -/
theorem tbl_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m')
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n)
    (hW : ∀ w ∈ W, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t) :
    m' (off base (bitsAt c.n j + t)) = m (off base (bitsAt c.n j + t)) :=
  hu.byte hW (by have := bitsAt_le c h7 hj; omega_using [hn, ht, this])

theorem tbl_apart_slW {l : List Nat} (hl : ∀ i ∈ l, i < 45) (j t : Nat) (ht : t < 64 * c.n)
    (hT : TMP ∉ l ∨ j ≠ 1 ∨ c.n ≠ 9 := by
      first | exact .inl (by decide) | exact .inr (.inl (by decide)) | exact .inr (.inr (by omega)))
    (hj4 : j < 4 := by omega) :
    ∀ w ∈ slW c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  rcases sl_apart_bits c (hl i hi) (hT.elim (fun h => .inl fun e => h (e ▸ hi)) .inr) (t + 1) (by omega_using [ht]) hj4
    with h | h
  · exact Or.inr (by dsimp only; omega_using [h])
  · exact Or.inl h

theorem tbl_apart_flag (h0 : 0 < c.n) (j t : Nat) :
    ∀ w ∈ [(c.sl FLAG, 8)], bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_below_bits c (i := FLAG) (by decide) j t
  exact Or.inr (by dsimp only; omega_using [h0, this])

/-- Tables `j ≠ j'` are apart. -/
theorem tbl_apart_tbl {j j' t : Nat} (hjj : j ≠ j') (ht : t < 64 * c.n) :
    ∀ w ∈ [(bitsAt c.n j', 64 * c.n)], bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  simp only [bitsAt_eq]
  rcases Nat.lt_or_gt_of_ne hjj with h | h
  · have := Nat.mul_le_mul_left (64 * c.n + 8) h
    rw [Nat.mul_succ] at this
    omega_using [ht, this]
  · have := Nat.mul_le_mul_left (64 * c.n + 8) h
    rw [Nat.mul_succ] at this
    omega_using [this]

/-- The moduli, from their slots. -/
theorem modP_of (hc : BaseCfgOk c) {base : Addr} {m : Mem} (h : wordsVal m base (c.sl MP) c.n = c.C.p) :
    ModOkW c.MP' size c.C.p m base :=
  ⟨hc.n0, sl_le c hc.n10 (by decide), sl_le c hc.n10 (by decide), sl_apart c (by decide), h,
    hc.minv_p, hc.red_p⟩

theorem modN_of (hc : BaseCfgOk c) {base : Addr} {m : Mem} (h : wordsVal m base (c.sl MN) c.n = c.C.n) :
    ModOkW c.MN' size c.C.n m base :=
  ⟨hc.n0, sl_le c hc.n10 (by decide), sl_le c hc.n10 (by decide), sl_apart c (by decide), h,
    hc.minv_n, hc.red_n⟩

theorem rsi_not_clob (n : Nat) : Reg.rsi ∉ clob n := by
  intro h
  rcases List.mem_append.mp h with h | h
  swap
  · split at h <;> simp at h
  simp only [List.mem_cons] at h
  rcases h with h | h | h | h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd (List.mem_of_mem_take h) (by decide)

theorem rsi_not_powClob (n : Nat) : Reg.rsi ∉ powClob n := by
  intro h'
  rcases List.mem_cons.mp h' with h' | h'
  · exact absurd h' (by decide)
  · exact rsi_not_clob n h'

end VG.Proof.Ecdsa.X86_64
