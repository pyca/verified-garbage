import VerifiedGarbage.Proof.Ecdsa.Arm.Layout

/-!
# ECDSA on 32-bit ARM: the setup

`Cfg.setupWith A` loads the working space's base from the stack argument
into `r12` (`wp_ldrSp`), saves `r4`–`r11` and `lr` at its start (`strs_ok`),
moves `out` to `lr`, reads `k`, `d` and the hash big-endian into their slots from the
registers `A` names (`setupLoad_ok`), stores the constants
(`setupConsts_ok`, by induction on the list) and sets the flag to all ones:
`setup_ok`, the state `SetupPost` describes.
-/

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str wp_dp wp_mov op2_imm op2_reg dpVal)

/-- A 32-bit word apart from the ranges. -/
theorem Unch.readW32 {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    {d : Nat} (hd : ∀ w ∈ W, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  (Mem.readW_congr fun i hi => (h _ fun w hw' => by
    rw [ofs_off base (by omega)]; have := hd w hw'; omega).symm).symm

/-- `ldr t, [sp, #off]`. -/
theorem wp_ldrSp {s : State} {is : List Instr} {Q : State → Prop} {t : Reg} {off : Nat} (ho : off < 4096)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4)
    (k : ∀ s', Upd s s' t (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (by simp only [exec, ho, ite_true, State.load32, hin, Option.map_some])
    (k _ (Upd.setReg _ _ _))

/-- Stores of registers at offsets of the working space, apart from each other. -/
theorem strs_ok {s : State} {base : Addr} {sz : Nat} (hs : Scr s base sz) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ sz) →
    l.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) →
    WP isa (.block (l.map fun p => .str p.1 wb p.2)) s fun s' =>
      Rest [] s s' ∧ Outs base (l.map fun p => (p.2, 4)) s.mem s'.mem ∧
      ∀ p ∈ l, s'.mem.readW (off base p.2) 32 = s.gpr p.1
  | [], _, _ => WP.block_nil ⟨Rest.refl _ _, Outs.refl _ _ _, fun _ h => absurd h List.not_mem_nil⟩
  | p :: l, hl, hp => by
    have hn := hs.nowrap
    have h0 := hl p List.mem_cons_self
    rw [List.pairwise_cons] at hp
    rw [List.map_cons]
    refine wp_str (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.write h0) fun s₁ m₁ => ?_
    have hs₁ := hs.of_rest (m₁.rest []) (by decide)
    refine WP.mono (strs_ok hs₁ l (fun q h => hl q (List.mem_cons_of_mem _ h)) hp.2) fun s' ⟨K, O, V⟩ => ?_
    have O₁ : Outside base p.2 4 s.mem s₁.mem := by rw [m₁.mem]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨(m₁.rest _).trans K, ?_, fun q hq => ?_⟩
    · rw [List.map_cons]
      exact (Outs.of_outside O₁ List.mem_cons_self).trans (O.mono fun r hr => List.mem_cons_of_mem _ hr)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [Unch.readW32 (VG.Proof.Weierstrass.Arm.Outs.unch O) (fun w hw => by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
          exact hp.1 r hr) (by omega), m₁.mem, Mem.readW_writeW_self32]
      · rw [V q hq, m₁.gpr]

/-- Loads of registers (not `r12`) from offsets of the working space. -/
theorem ldrs_ok {s : State} {base : Addr} {sz : Nat} (hs : Scr s base sz) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ sz) → (l.map Prod.fst).Nodup → (∀ p ∈ l, p.1 ≠ .r12) →
    WP isa (.block (l.map fun p => .ldr p.1 wb p.2)) s fun s' =>
      s'.mem = s.mem ∧ Rest (l.map Prod.fst) s s' ∧
      ∀ p ∈ l, s'.gpr p.1 = s.mem.readW (off base p.2) 32
  | [], _, _, _ => WP.block_nil ⟨rfl, Rest.refl _ _, fun _ h => absurd h List.not_mem_nil⟩
  | p :: l, hl, hnd, h12 => by
    have hn := hs.nowrap
    have h0 := hl p List.mem_cons_self
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons]
    refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read h0) fun s₁ u₁ => ?_
    have hs₁ := hs.of_rest (u₁.rest (ws := [p.1]) (by simp)) (by simpa using (h12 p List.mem_cons_self).symm)
    refine WP.mono (ldrs_ok hs₁ l (fun q h => hl q (List.mem_cons_of_mem _ h)) hnd.2
      (fun q h => h12 q (List.mem_cons_of_mem _ h))) fun s' ⟨M, K, V⟩ => ?_
    refine ⟨by rw [M, u₁.mem], ((u₁.rest (by simp)).trans (K.mono fun r hr => by simp [hr])), fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [K.gpr _ hnd.1, u₁.gpr]
    · rw [V q hq, u₁.mem]

/-! ## Reading `k`, `d` and the hash -/

/-- The `8 n` bytes at `p` (readable, outside the working space, and so
unchanged since `s`) to slot `i`. -/
theorem setupLoad_ok {c : Cfg} (hc : CfgOk c) {s t : State} {base : Addr} {i : Nat} {src : Reg}
    {p : BitVec 32} (hs : Scr t base size) (hi : i < 45) (hsrc : src ≠ .r4) (hp : t.gpr src = p)
    (hfit : p.toNat + 8 * c.n ≤ 2 ^ 32)
    (hin : ∀ e, e + 4 ≤ 8 * c.n → InRegions (t.rd ++ t.wr) (State.addr p + BitVec.ofNat 64 e) 4)
    (hd : Region.Disjoint ⟨State.addr p, 8 * c.n⟩ ⟨base, size⟩) (ho : Outside base 0 size s.mem t.mem) :
    WP isa (.block (loadBE c.n (c.sl i) src)) t fun t' =>
      wordsVal t'.mem base (c.sl i) c.n = ofBytes (Spec.Ecdsa.bytesAt s.mem (State.addr p) (8 * c.n)) ∧
      Rest [.r4] t t' ∧ Outside base (c.sl i) (8 * c.n) t.mem t'.mem := by
  have hl := sl_le c hc.n10 hi
  have h7 := hc.n10
  refine WP.mono (loadBE_ok hs hsrc hl (by rw [hp]; exact hfit) (by rw [hp]; exact hin)
    (by rw [hp]; exact hd.sub_right (Offset.sub_base base hl))) fun t' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  have hb : Spec.Ecdsa.bytesAt t.mem (State.addr p) (8 * c.n) = Spec.Ecdsa.bytesAt s.mem (State.addr p) (8 * c.n) :=
    List.map_congr_left fun j hj =>
      keep_of_disjoint' ho hd (by decide) (List.mem_range.mp hj) (by omega)
  rw [e, hp, hb]

/-! ## The constants -/

/-- The constants of `l`, apart slots below `17`, each in its slot; only their
slots change. -/
theorem setupConsts_ok {c : Cfg} (hc : CfgOk c) {base : Addr} : ∀ (l : List (Nat × Nat)) {t : State},
    Scr t base size → (∀ ix ∈ l, ix.1 < 17 ∧ ix.2 < 2 ^ (64 * c.n)) → (l.map Prod.fst).Nodup →
    WP isa (.block (l.flatMap (fun (i, x) => setConst c.n (c.sl i) x))) t fun t' =>
      (∀ ix ∈ l, wordsVal t'.mem base (c.sl ix.1) c.n = ix.2) ∧ Rest [.r4] t t' ∧
      Unch base (l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem
  | [], _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, Rest.refl _ _,
      Unch.refl _ _ _⟩
  | (i, x) :: l, t, hs, hb, hnd => by
    rw [List.flatMap_cons]
    have hi := hb (i, x) List.mem_cons_self
    have hl := sl_le c hc.n10 (i := i) (by omega)
    refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs hl hi.2) fun t₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_rest k₁ (by decide)
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

theorem saveCode_eq : Cfg.saveCode = Cfg.saved.map fun p => .str p.1 wb p.2 := rfl

theorem saved_pairwise : Cfg.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by decide

theorem saved_lt : ∀ p ∈ Cfg.saved, p.2 + 4 ≤ 36 := by decide

theorem saved_r12 : ∀ p ∈ Cfg.saved, p.1 ≠ .r12 ∧ p.1 ≠ .r0 := by decide

/-- The working space's base to `r12`. -/
theorem scStart_ok {A : Args} {s : State} {is : List Instr} {Q : State → Prop}
    (hin : A.sc = none → InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4)
    (k : ∀ s₁, Upd s s₁ .r12 (scVal A s) → WP isa (.block is) s₁ Q) :
    WP isa (.block (Cfg.scStart A :: is)) s Q := by
  obtain ⟨ak, ad, ae, _ | r⟩ := A
  · have ha : State.addr (s.sp + BitVec.ofNat 32 0) = stackArgAddr s 0 := by simp [stackArgAddr]
    refine wp_ldrSp (by decide) (by rw [ha]; exact hin rfl) fun s₁ u₁ => k s₁ ?_
    rw [ha] at u₁
    exact u₁
  · exact wp_mov (op2_reg _ _) fun s₁ u₁ => k s₁ u₁

theorem setup_eq (c : Cfg) (A : Args) : c.setupWith A = Cfg.scStart A :: (Cfg.saveCode ++
    (.mov .lr (.reg .r0) :: (loadBE c.n (c.sl K) A.k ++ (loadBE c.n (c.sl D) A.d ++
    (loadBE c.n (c.sl E) A.e ++ (c.consts.flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
    ([.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.imm 1), .str .r4 wb (c.sl FLAG)] : List Instr))))))) := by
  simp only [Cfg.setupWith, List.append_assoc, List.cons_append, List.nil_append]

theorem setup_ok {c : Cfg} (hc : CfgOk c) {A : Args} {s : State} (hp : SetupPre c A s) :
    WP isa (.block (c.setupWith A)) s (SetupPost c A s (scBase A s)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hsz : size = 4096 := rfl
  have hfit := hp.sc_fit
  obtain ⟨hk4, hd4, he4⟩ := hp.args
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk4 hd4 he4
  rw [setup_eq]
  -- The working space's base.
  refine scStart_ok hp.sc_in fun s₁ u₁ => ?_
  have hb₁ : State.addr (s₁.gpr .r12) = scBase A s := by rw [u₁.gpr]
  have hs₁ : Scr s₁ (scBase A s) size := ⟨hb₁, ⟨8192, by decide, by decide, by rw [u₁.wr]; exact hp.wr⟩,
    by simp only [scBase, State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]; omega, by decide⟩
  have hn := hs₁.nowrap
  -- The saves.
  rw [saveCode_eq]
  refine VG.Proof.X25519.Arm.WP.append (strs_ok hs₁ Cfg.saved (fun p hp' => by have := saved_lt p hp'; omega)
    saved_pairwise) fun s₂ ⟨K₂, O₂, V₂⟩ => ?_
  have hs₂ := hs₁.of_rest K₂ (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  have hs₃ := hs₂.of_rest (u₃.rest (ws := [.lr]) (by simp)) (by decide)
  have K₃ : Rest [.r12, .lr] s s₃ := (u₁.rest (by simp)).trans ((K₂.mono (by simp)).trans (u₃.rest (by simp)))
  have lr₃ : s₃.gpr .lr = s.gpr .r0 := by
    rw [u₃.gpr, K₂.gpr _ (by simp), u₁.other _ (by decide)]
  have O₂' : Outside (scBase A s) 0 36 s₁.mem s₂.mem := fun x hx => O₂ x fun w hw => by
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hw
    have := saved_lt p hp'
    dsimp only; omega
  have O₃ : Outside (scBase A s) 0 size s.mem s₃.mem := by
    rw [← u₁.mem, u₃.mem]
    exact O₂'.mono (Nat.le_refl _) (by omega)
  have RW₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [K₃.rd, K₃.wr]
  -- `k`
  refine VG.Proof.X25519.Arm.WP.append (setupLoad_ok hc (s := s) hs₃ (i := K) (by decide) hk4.1
    (K₃.gpr _ (by simpa using hk4.2)) hp.k_fit (by rw [RW₃]; exact hp.k_in) hp.k_sc O₃) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_rest k₄ (by decide)
  have K₄ : Rest [.r4, .r12, .lr] s s₄ := (K₃.mono (by simp)).trans (k₄.mono (by simp))
  have O₄' : Outside (scBase A s) 0 size s.mem s₄.mem :=
    O₃.trans (O₄.mono (Nat.zero_le _) (by have := sl_le c h7 (i := K) (by decide); omega))
  -- `d`
  refine VG.Proof.X25519.Arm.WP.append (setupLoad_ok hc (s := s) hs₄ (i := D) (by decide) hd4.1
    (K₄.gpr _ (by simpa using hd4)) hp.d_fit (by rw [K₄.rd, K₄.wr]; exact hp.d_in) hp.d_sc O₄')
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_rest k₅ (by decide)
  have K₅ : Rest [.r4, .r12, .lr] s s₅ := K₄.trans (k₅.mono (by simp))
  have O₅' : Outside (scBase A s) 0 size s.mem s₅.mem :=
    O₄'.trans (O₅.mono (Nat.zero_le _) (by have := sl_le c h7 (i := D) (by decide); omega))
  -- the hash
  refine VG.Proof.X25519.Arm.WP.append (setupLoad_ok hc (s := s) hs₅ (i := E) (by decide) he4.1
    (K₅.gpr _ (by simpa using he4)) hp.e_fit (by rw [K₅.rd, K₅.wr]; exact hp.e_in) hp.e_sc O₅')
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_rest k₆ (by decide)
  -- the constants
  refine VG.Proof.X25519.Arm.WP.append (setupConsts_ok hc c.consts hs₆ (consts_bounds hc) (consts_nodup c))
    fun s₇ ⟨e₇, k₇, U₇⟩ => ?_
  have hs₇ := hs₆.of_rest k₇ (by decide)
  have hsl0 : c.sl 0 = 64 := by rw [sl_eq]; omega
  have O₇ : Outside (scBase A s) (c.sl 0) (8 * c.n * 17) s₆.mem s₇.mem := U₇.outside fun w hw => by
    obtain ⟨ix, hix, rfl⟩ := List.mem_map.mp hw
    have := sl_lt c (consts_bounds hc ix hix).1
    have : c.sl 0 ≤ c.sl ix.1 := by rw [hsl0, sl_eq]; omega
    exact ⟨this, by rw [sl_eq c 17] at *; omega⟩
  -- the flag
  refine wp_mov (op2_imm (by decide)) fun s₈ u₈ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₉ u₉ => ?_
  have k₉ : Rest [.r4] s₇ s₉ := (u₈.rest (by simp)).trans (u₉.rest (by simp))
  have hs₉ := hs₇.of_rest k₉ (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine wp_str (hs₁.off_lt (by omega)) (hs₉.ea (d := c.sl FLAG) (by omega))
    (hs₉.write (d := c.sl FLAG) (n := 4) (by omega)) fun s' m' => WP.block_nil ?_
  have O' : Outside (scBase A s) (c.sl FLAG) 4 s₇.mem s'.mem := by
    rw [m'.mem, u₉.mem, u₈.mem]; exact writeW32_outside _ _ _ (by omega)
  -- Everything after the saves writes only in `[64, size)`.
  have h17 := sl_le c h7 (i := 17) (by decide)
  have hK := sl_le c h7 (i := K) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hK17 := sl_lt c (i := 17) (j := K) (by decide)
  have hDK := sl_lt c (i := K) (j := D) (by decide)
  have hED := sl_lt c (i := D) (j := E) (by decide)
  have hFE := sl_lt c (i := E) (j := FLAG) (by decide)
  have h0' : c.sl 0 + 8 * c.n * 17 = c.sl 17 := by rw [sl_eq, sl_eq]; omega
  have Ol : Outside (scBase A s) 64 (size - 64) s₃.mem s'.mem := by
    exact ((((O₄.mono (by omega) (by omega)).trans (O₅.mono (by omega) (by omega))).trans
      (O₆.mono (by omega) (by omega))).trans (O₇.mono (by omega) (by omega))).trans
      (O'.mono (by omega) (by omega))
  have K' : Rest [.r4, .r12, .lr] s s' := (K₅.trans (k₆.mono (by simp))).trans ((k₇.mono (by simp)).trans
    ((k₉.mono (by simp)).trans (m'.rest _)))
  have K₃' : Rest [.r4, .r12] s₃ s' := ((k₄.mono (by simp)).trans (k₅.mono (by simp))).trans
    ((k₆.mono (by simp)).trans ((k₇.mono (by simp)).trans ((k₉.mono (by simp)).trans (m'.rest _))))
  refine ⟨hs₉.of_rest (m'.rest []) (by decide), ⟨by rw [K'.wr]; exact hp.wr,
    by simp only [scBase, State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]; omega⟩, K', ?_, fun rd hrd => ?_, ?_, ?_, ?_, ?_, fun ix hix => ?_, ?_⟩
  · exact (O₃.trans (Ol.mono (Nat.zero_le _) (by omega))).unch
  · have hlt := saved_lt rd hrd
    have hw32 := Ol.w32 (d := rd.2) (by omega) (by omega)
    rw [BitVec.eq_of_toNat_eq hw32, u₃.mem, V₂ rd hrd, u₁.other _ (saved_r12 rd hrd).1]
  · rw [K₃'.gpr _ (by decide), lr₃]
  · show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega) (by omega),
      O₇.wordsVal (by omega) (by omega), O₆.wordsVal (by omega) (by omega),
      O₅.wordsVal (by omega) (by omega), e₄]
  · show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega) (by omega),
      O₇.wordsVal (by omega) (by omega), O₆.wordsVal (by omega) (by omega), e₅]
  · show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega) (by omega),
      O₇.wordsVal (by omega) (by omega), e₆]
  · have := sl_lt c (consts_bounds hc ix hix).1
    have := sl_lt c (i := ix.1) (j := FLAG) (by have := (consts_bounds hc ix hix).1; show ix.1 < 44; omega)
    have := sl_le c h7 (i := ix.1) (by have := (consts_bounds hc ix hix).1; omega)
    show wordsVal s'.mem _ _ _ = _
    rw [(O'.unch).wordsVal (fun w hw => by simp at hw; rw [hw]; simp; omega) (by omega), e₇ ix hix]
  · rw [flagW, m'.mem, Mem.readW_writeW_self32, u₉.gpr, dpVal, u₈.gpr]; rfl

end VG.Proof.Ecdsa.Arm
