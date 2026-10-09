import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Loop

/-!
# The `zmm` comb: the rows of the `zmm` code

`zconsts` doubles the window's constant rows and slot 15's `2` into the rows
of the `zmm` code (`zrow`, `ZK2`), builds the blends' masks (`vpblendd` of
zero and all ones, the masks themselves), and copies the lanes of the point
to both halves.
-/

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64.Ifma
  VG.Proof.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y ld v zero blend KM K19 KB0 KB1)
open VG.Impl.Ed25519.X86_64.Ifma (EK13 EK26 EK39)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr mq)
open VG.Proof.X25519.X86_64 (off ofs Outside Keeps clob)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

theorem cat_extract (x : BitVec 256) : x.extractLsb' 128 128 ++ x.extractLsb' 0 128 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_append]
  by_cases h : j < 128
  · rw [ite_eq_left h, BitVec.getLsbD_extractLsb', decide_eq_true h, Bool.true_and, Nat.zero_add]
  · rw [ite_eq_right h, BitVec.getLsbD_extractLsb', decide_eq_true (show j - 128 < 128 by omega), Bool.true_and,
      show 128 + (j - 128) = j by omega]

/-- The 32-byte row at `o` copied to both halves of the 64-byte row at `d`, through `ymm9`. -/
theorem rowCopy_ok {s : State} {b : Addr} (hs : Scratch s b) {o d : Nat} (ho : o + 32 ≤ 8192)
    (hd : d + 64 ≤ 8192) :
    WP isa (.block (ld 9 o :: dupStore d)) s fun t =>
      (∀ i < 64, t.mem (b + BitVec.ofNat 64 (d + i)) = s.mem (b + BitVec.ofNat 64 (o + i % 32))) ∧
      (∀ a, ¬ (d ≤ ofs b a ∧ ofs b a < d + 64) → t.mem a = s.mem a) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms ∧
      (∀ r, r ≠ y 9 → ∀ i < 4, t.zlane r i = s.zlane r i) := by
  let w := s.mem.readW (b + BitVec.ofNat 64 o) 256
  let s₁ := s.setV .l256 (y 9) (w.extractLsb' 0 128) (w.extractLsb' 128 128)
  let s₂ := (ZOp.vshufi32x4 (y 9) (y 9) (y 9) 0x44).exec s₁
  have hin : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 o) 32 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base b ho (by omega)⟩
  have hw : InRegions s₂.wr (b + BitVec.ofNat 64 d) 64 := ⟨_, hs.wr, Offset.contains_base b hd (by omega)⟩
  have l₂ : ∀ i < 4, s₂.zlane (y 9) i = w.extractLsb' (128 * (i % 2)) 128 := fun i hi => by
    simp only [s₂, zlane_zlo _ _ _ _ _ hi, ite_true, s₁, zlane_setV256 _ _ _ _ _ hi,
      zlane_setV256 _ _ _ _ _ (show i - 2 < 4 by omega)]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  have e₁ : exec (ld 9 o) s = some s₁ := by
    simp only [exec, ld, ea_sc' hs.rdi, State.load256, hin, ite_true, Option.map_some]; rfl
  have e₃ : exec (.vmovdqu32Store (sc d) (y 9)) s₂ =
      some (s₂.setMem (s₂.mem.writeW (b + BitVec.ofNat 64 d) (s₂.zmm (y 9)))) := by
    simp only [exec, ea_sc' (show s₂.gpr .rdi = b from hs.rdi), State.store512_eq, hw, ite_true]
  refine WP.of_runBlock ⟨_, runBlock_three e₁ rfl e₃, ?_⟩
  refine ⟨fun i hi => ?_, fun a ha => ?_, by zkeep, by zkeep, by zkeep, by zkeep, fun r hr i hi => ?_⟩
  · simp only [State.setMem]
    rw [← Offset.add_ofNat_add_ofNat, writeW_byte _ _ _ (by omega) (by decide)]
    rw [show i = 32 * (i / 32) + i % 32 by omega, zmm_byte s₂ (y 9) (by omega) (by omega),
      l₂ _ (by omega), l₂ _ (by omega), show (2 * (i / 32) + 1) % 2 = 1 by omega,
      show 2 * (i / 32) % 2 = 0 by omega, Nat.mul_one, Nat.mul_zero, cat_extract,
      byte_readW _ _ (by omega), Offset.add_ofNat_add_ofNat]
    congr 3; omega
  · simp only [State.setMem]
    refine (writeW_byte_off _ _ _ _ ?_).trans rfl
    simp only [ofs] at ha
    rw [sub_off]; have := (a - b).isLt; omega
  · simp only [State.setMem_zlane, s₂, zlane_zlo _ _ _ _ _ hi, hr, ite_false, s₁, zlane_setV256 _ _ _ _ _ hi]


/-- Rows copied, each `(source, destination)` of `L`: sources below 4096, destinations from 4096
up, apart. -/
theorem rowsCopy_ok {b : Addr} : ∀ (L : List (Nat × Nat)) (s : State), Scratch s b →
    (∀ e ∈ L, e.1 + 32 ≤ 4096 ∧ 4096 ≤ e.2 ∧ e.2 + 64 ≤ 8192) →
    L.Pairwise (fun e f => e.2 + 64 ≤ f.2 ∨ f.2 + 64 ≤ e.2) →
    WP isa (.block (L.flatMap fun e => ld 9 e.1 :: dupStore e.2)) s fun t =>
      (∀ e ∈ L, ∀ i < 64, t.mem (b + BitVec.ofNat 64 (e.2 + i)) = s.mem (b + BitVec.ofNat 64 (e.1 + i % 32))) ∧
      (∀ a, (∀ e ∈ L, ¬ (e.2 ≤ ofs b a ∧ ofs b a < e.2 + 64)) → t.mem a = s.mem a) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms ∧
      (∀ r, r ≠ y 9 → ∀ i < 4, t.zlane r i = s.zlane r i)
  | [], s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | e :: L, s, hs, hL, hp => by
    rw [List.flatMap_cons, WP.block_append_iff]
    have he := hL e List.mem_cons_self
    refine WP.mono (rowCopy_ok hs (o := e.1) (d := e.2) (by omega) he.2.2) fun s₁ ⟨c₁, f₁, g₁, rd₁, wr₁, sy₁, z₁⟩ => ?_
    have hs₁ : Scratch s₁ b := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
    have hp' := List.pairwise_cons.1 hp
    refine WP.mono (rowsCopy_ok L s₁ hs₁ (fun f hf => hL f (List.mem_cons_of_mem _ hf)) hp'.2)
      fun t ⟨c, f, g, rd, wr, sy, z⟩ => ⟨fun e' he' i hi => ?_, fun a ha => ?_, by rw [g, g₁], by rw [rd, rd₁],
        by rw [wr, wr₁], by rw [sy, sy₁], fun r hr i hi => by rw [z r hr i hi, z₁ r hr i hi]⟩
    · rcases List.mem_cons.1 he' with rfl | he'
      · rw [f _ (fun f hf => by
          have := hp'.1 f hf
          simp only [ofs]; rw [off_ofNat _ (by omega)]; omega), c₁ i hi]
      · have hf := hL e' (List.mem_cons_of_mem _ he')
        rw [c e' he' i hi, f₁ _ (by simp only [ofs]; rw [off_ofNat _ (by omega)]; omega)]
    · rw [f a (fun f hf => ha f (List.mem_cons_of_mem _ hf)), f₁ a (ha e List.mem_cons_self)]

/-- Lane `i` of a `zmm` register. -/
theorem zmm_lane (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    (s.zmm r).extractLsb' (128 * i) 128 = s.zlane r i := by
  have e := zmm_half s r (h := i / 2) (by omega)
  rw [show 128 * i = 256 * (i / 2) + 128 * (i % 2) by omega,
    ← extract_extract _ (256 * (i / 2)) 256 (128 * (i % 2)) 128 (by omega), e]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hj, Bool.true_and]
  rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with h | h
  · rw [h, ite_eq_left (by omega), show 2 * (i / 2) = i by omega, Nat.mul_zero, Nat.zero_add]
  · rw [h, ite_eq_right (by omega), show 2 * (i / 2) + 1 = i by omega, Nat.mul_one, Nat.add_sub_cancel_left]


/-- All ones, as `vpcmpeqd` of a register with itself leaves it. -/
abbrev ones128 : BitVec 128 := ofDwords 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF

theorem pcmpeqd_self (x : BitVec 128) : XBinOp.eval .pcmpeqd x x = ones128 := by
  simp only [XBinOp.eval, ite_true]

theorem blend_ones (n : BitVec 4) : blendDwords 0 ones128 n = maskLane n := by
  have d0 : ∀ k < 4, dword (0 : BitVec 128) k = 0 := fun k hk => by
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [dword]
  simp only [blendDwords, maskLane, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
    d0 0 (by decide), d0 1 (by decide), d0 2 (by decide), d0 3 (by decide)]
  rfl

/-- The masks of `sel` (from zero in `ymm10` and all ones in `ymm11`) to both halves of the
64-byte row at `d`. -/
theorem maskCopy_ok {s : State} {b : Addr} (hs : Scratch s b) {d : Nat} (hd : d + 64 ≤ 8192) (sel : BitVec 8)
    (h10 : ∀ k < 2, s.lane (y 10) k = 0) (h11 : ∀ k < 2, s.lane (y 11) k = ones128) :
    WP isa (.block (blend 9 10 11 sel :: dupStore d)) s fun t =>
      (∀ i < 4, (t.mem.readW (b + BitVec.ofNat 64 d) 512).extractLsb' (128 * i) 128 =
        maskLane (sel.extractLsb' (4 * (i % 2)) 4)) ∧
      (∀ a, ¬ (d ≤ ofs b a ∧ ofs b a < d + 64) → t.mem a = s.mem a) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms ∧
      (∀ r, r ≠ y 9 → ∀ i < 4, t.zlane r i = s.zlane r i) := by
  let s₁ := (VOp.vpblendd .l256 (y 9) (y 10) (y 11) sel).exec s
  let s₂ := (ZOp.vshufi32x4 (y 9) (y 9) (y 9) 0x44).exec s₁
  have hw : InRegions s₂.wr (b + BitVec.ofNat 64 d) 64 := ⟨_, hs.wr, Offset.contains_base b hd (by omega)⟩
  have e₃ : exec (.vmovdqu32Store (sc d) (y 9)) s₂ =
      some (s₂.setMem (s₂.mem.writeW (b + BitVec.ofNat 64 d) (s₂.zmm (y 9)))) := by
    simp only [exec, ea_sc' (show s₂.gpr .rdi = b from hs.rdi), State.store512_eq, hw, ite_true]
  refine WP.of_runBlock ⟨_, runBlock_three rfl rfl e₃, ?_⟩
  refine ⟨fun i hi => ?_, fun a ha => ?_, by zkeep, by zkeep, by zkeep, by zkeep, fun r hr i hi => ?_⟩
  · simp only [State.setMem]
    have e : (s₂.mem.writeW (b + BitVec.ofNat 64 d) (s₂.zmm (y 9))).readW (b + BitVec.ofNat 64 d) 512 =
        s₂.zmm (y 9) := Mem.readW_writeW_self _ _ 64 _ (by decide)
    rw [e, zmm_lane _ _ hi]
    simp only [s₂, zlane_zlo _ _ _ _ _ hi, ite_true, s₁, VOp.exec]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      simp only [zlane_setV256 _ _ _ _ _ (show (0 : Nat) < 4 by decide),
        zlane_setV256 _ _ _ _ _ (show (1 : Nat) < 4 by decide), ite_true, h10 0 (by decide), h10 1 (by decide),
        h11 0 (by decide), h11 1 (by decide), blend_ones] <;> simp
  · simp only [State.setMem]
    refine (writeW_byte_off _ _ _ _ ?_).trans rfl
    simp only [ofs] at ha
    rw [sub_off]; have := (a - b).isLt; omega
  · simp only [State.setMem_zlane, s₂, zlane_zlo _ _ _ _ _ hi, hr, ite_false, s₁, VOp.exec,
      zlane_setV256 _ _ _ _ _ hi]

/-- The masks of the selectors `k < n` of `blendSels`, to their rows. -/
theorem masksCopy_ok {b : Addr} : ∀ n ≤ 4, ∀ (s : State), Scratch s b →
    (∀ k < 2, s.lane (y 10) k = 0) → (∀ k < 2, s.lane (y 11) k = ones128) →
    WP isa (.block ((List.range n).flatMap fun k =>
        blend 9 10 11 (blendSels.getD k 0) :: dupStore (ZMASK + 64 * k))) s fun t =>
      (∀ k < n, ∀ i < 4, (t.mem.readW (b + BitVec.ofNat 64 (ZMASK + 64 * k)) 512).extractLsb' (128 * i) 128 =
        maskLane ((blendSels.getD k 0).extractLsb' (4 * (i % 2)) 4)) ∧
      (∀ a, ¬ (ZMASK ≤ ofs b a ∧ ofs b a < ZMASK + 64 * n) → t.mem a = s.mem a) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms ∧
      (∀ r, r ≠ y 9 → ∀ i < 4, t.zlane r i = s.zlane r i)
  | 0, _, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl,
      rfl, fun _ _ _ _ => rfl⟩
  | n + 1, hn, s, hs, h10, h11 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (masksCopy_ok n (by omega) s hs h10 h11) fun s₁ ⟨c₁, f₁, g₁, rd₁, wr₁, sy₁, z₁⟩ => ?_
    have hs₁ : Scratch s₁ b := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
    have l : ∀ r, r ≠ y 9 → ∀ k < 2, s₁.lane r k = s.lane r k := fun r hr k hk => by
      have := z₁ r hr k (by omega)
      simp only [State.zlane, show k < 2 from hk, ite_true] at this
      exact this
    refine WP.mono (maskCopy_ok hs₁ (d := ZMASK + 64 * n) (by unfold ZMASK; omega) (blendSels.getD n 0)
      (fun k hk => by rw [l _ (by decide) k hk]; exact h10 k hk)
      (fun k hk => by rw [l _ (by decide) k hk]; exact h11 k hk))
      fun t ⟨c, f, g, rd, wr, sy, z⟩ => ⟨fun k hk i hi => ?_, fun a ha => ?_, by rw [g, g₁], by rw [rd, rd₁],
        by rw [wr, wr₁], by rw [sy, sy₁], fun r hr i hi => by rw [z r hr i hi, z₁ r hr i hi]⟩
    · by_cases hkn : k = n
      · subst hkn; exact c i hi
      · rw [← c₁ k (by omega) i hi]
        refine congrArg (BitVec.extractLsb' (128 * i) 128) ?_
        refine Mem.readW_congr fun q hq => f _ ?_
        simp only [ofs, Offset.add_ofNat_add_ofNat]
        rw [off_ofNat _ (by unfold ZMASK; omega)]; unfold ZMASK at *; omega
    · rw [f a (fun h => ha (by unfold ZMASK at *; omega)), f₁ a (fun h => ha (by unfold ZMASK at *; omega))]

/-- The lanes of `ymm0–ymm(n-1)` copied to both halves. -/
theorem dups_ok : ∀ n ≤ 5, ∀ (s : State),
    WP isa (.block ((List.range n).map fun j => zlo j j j)) s fun t =>
      (∀ j < n, ∀ i < 4, t.zlane (y j) i = s.zlane (y j) (i % 2)) ∧
      (∀ r, (∀ j < n, r ≠ y j) → ∀ i < 4, t.zlane r i = s.zlane r i) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms
  | 0, _, s => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, hn, s => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (dups_ok n (by omega) s) fun s₁ ⟨c₁, f₁, m₁, g₁, rd₁, wr₁, sy₁⟩ => ?_
    refine WP.of_runBlock ⟨_, runBlock_one rfl, fun j hj i hi => ?_, fun r hr i hi => ?_, m₁, g₁, rd₁, wr₁, sy₁⟩
    · have hne : ∀ j < n, y n ≠ y j := fun j hj => by
        have : ∀ a < 5, ∀ c < 5, a ≠ c → y a ≠ y c := by decide
        exact this n (by omega) j (by omega) (by omega)
      rw [zlane_zlo _ _ _ _ _ hi]
      by_cases hjn : j = n
      · subst hjn
        rw [ite_eq_left rfl, f₁ _ hne _ (by omega)]
        split
        · rw [Nat.mod_eq_of_lt (by omega)]
        · rw [f₁ _ hne _ (by omega), show i - 2 = i % 2 by omega]
      · have hne' : y j ≠ y n := by
          have : ∀ a < 5, ∀ c < 5, a ≠ c → y a ≠ y c := by decide
          exact this j (by omega) n (by omega) hjn
        rw [ite_eq_right hne', c₁ j (by omega) i hi]
    · rw [zlane_zlo _ _ _ _ _ hi, ite_eq_right (hr n (by omega)), f₁ r (fun j hj => hr j (by omega)) i hi]

/-- The rows `zconsts` copies. -/
abbrev zrowList : List (Nat × Nat) :=
  [(KM, zrow KM), (K19, zrow K19), (KB0, zrow KB0), (KB1, zrow KB1), (offset 15, ZK2)]

theorem zconsts_split : zconsts = zrowList.flatMap (fun e => ld 9 e.1 :: dupStore e.2) ++
    ([zero 10, v .vpcmpeqd 11 11 11] : List Instr) ++
    ((List.range 4).flatMap fun k => blend 9 10 11 (blendSels.getD k 0) :: dupStore (ZMASK + 64 * k)) ++
    (List.range 5).map (fun j => zlo j j j) := rfl

theorem _root_.VG.Proof.Ed25519.X86_64.Ifma.EConsts.of_rows {m m' : Mem} {base : Addr} (hk : EConsts m base)
    (w : ∀ x, 1664 ≤ x → x < 1888 → m' (base + BitVec.ofNat 64 x) = m (base + BitVec.ofNat 64 x)) :
    EConsts m' base := by
  have e : ∀ d l, 1664 ≤ d → d + 8 * l + 8 ≤ 1888 → mq m' base (d + 8 * l) = mq m base (d + 8 * l) :=
    fun d l h1 h2 => Mem.readW_congr fun i hi => by
      try simp only [Offset.add_ofNat_add_ofNat]
      exact w _ (by omega) (by omega)
  exact ⟨⟨fun l hl => by rw [e _ _ (by decide) (by simp only [KM]; omega)]; exact hk.km l hl,
    fun l hl => by rw [e _ _ (by decide) (by simp only [K19]; omega)]; exact hk.k19 l hl,
    fun l hl => by rw [e _ _ (by decide) (by simp only [KB0]; omega)]; exact hk.kb0 l hl,
    fun l hl => by rw [e _ _ (by decide) (by simp only [KB1]; omega)]; exact hk.kb1 l hl⟩,
    fun l hl => by rw [e _ _ (by decide) (by simp only [EK13]; omega)]; exact hk.k13 l hl,
    fun l hl => by rw [e _ _ (by decide) (by simp only [EK26]; omega)]; exact hk.k26 l hl,
    fun l hl => by rw [e _ _ (by decide) (by simp only [EK39]; omega)]; exact hk.k39 l hl⟩

/-- The rows of the `zmm` code, and the point in both halves. -/
theorem zconsts_ok {s : State} {b : Addr} (hs : Scratch s b) (hk : EConsts s.mem b) :
    WP isa (.block zconsts) s fun t =>
      (∀ h < 2, EConsts (Zmm.half b h t).mem b) ∧
      (∀ sel ∈ blendSels, ∀ i < 4, (t.mem.readW (b + BitVec.ofNat 64 (maskRow sel)) 512).extractLsb' (128 * i) 128 =
        maskLane (sel.extractLsb' (4 * (i % 2)) 4)) ∧
      (∀ h < 2, VG.Proof.X25519.X86_64.F t.mem b (ZK2 + 32 * h) = VG.Proof.X25519.X86_64.F s.mem b (offset 15)) ∧
      (∀ a, ¬ (ZB ≤ ofs b a ∧ ofs b a < 6080) → t.mem a = s.mem a) ∧
      (∀ h < 2, ∀ r < 5, ∀ k < 4, qw (Zmm.half b h t) (xr r) k = qw s (xr r) k) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms := by
  rw [zconsts_split, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (rowsCopy_ok (b := b) zrowList s hs (by decide +kernel) (by decide +kernel))
    fun s₁ ⟨c₁, f₁, g₁, rd₁, wr₁, sy₁, z₁⟩ => ?_
  have hs₁ : Scratch s₁ b := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  let s₂ := (VOp.vbin .vpcmpeqd .l256 (y 11) (y 11) (y 11)).exec ((VOp.vbin .vpxor .l256 (y 10) (y 10) (y 10)).exec s₁)
  refine WP.of_runBlock ⟨s₂, by simp only [zero, v, runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  have hs₂ : Scratch s₂ b := ⟨hs₁.rdi, hs₁.wr, hs₁.nowrap⟩
  have h10 : ∀ k < 2, s₂.lane (y 10) k = 0 := fun k hk => by
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
      simp [s₂, VOp.exec, State.lane, State.setV, VBinOp.sse, XBinOp.eval, show y 10 ≠ y 11 by decide]
  have h11 : ∀ k < 2, s₂.lane (y 11) k = ones128 := fun k hk => by
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
      simp only [s₂, VOp.exec, State.lane, State.setV, VBinOp.sse, pcmpeqd_self, ↓reduceIte,
        show (1 : Nat) ≠ 0 by decide]
  have zl₂ : ∀ r, r ≠ y 10 → r ≠ y 11 → ∀ i < 4, s₂.zlane r i = s₁.zlane r i := fun r h1 h2 i hi => by
    simp only [s₂, VOp.exec, zlane_setV256 _ _ _ _ _ hi, h1, h2, ite_false]
  refine WP.mono (masksCopy_ok 4 (Nat.le_refl _) s₂ hs₂ h10 h11) fun s₃ ⟨c₃, f₃, g₃, rd₃, wr₃, sy₃, z₃⟩ => ?_
  refine WP.mono (dups_ok 5 (Nat.le_refl _) s₃) fun t ⟨c, f, m, g, rd, wr, sy⟩ => ?_
  -- the memory: the rows copied, then the masks
  have mt : ∀ a, ¬ (ZMASK ≤ ofs b a ∧ ofs b a < ZMASK + 64 * 4) → t.mem a = s₁.mem a := fun a ha => by
    rw [m, f₃ a ha]; rfl
  have row : ∀ e ∈ zrowList, ∀ i < 64,
      t.mem (b + BitVec.ofNat 64 (e.2 + i)) = s.mem (b + BitVec.ofNat 64 (e.1 + i % 32)) := fun e he i hi => by
    have := (show ∀ e ∈ zrowList, (e.2 + 64 ≤ ZMASK ∨ ZMASK + 64 * 4 ≤ e.2) ∧ e.2 + 64 ≤ 8192 by decide +kernel) e he
    rw [mt _ (by simp only [ofs]; rw [off_ofNat _ (by omega)]; omega), c₁ e he i hi]
  have frame : ∀ a, ¬ (ZB ≤ ofs b a ∧ ofs b a < 6080) → t.mem a = s.mem a := fun a ha => by
    rw [mt a (fun h => ha (by unfold ZMASK ZB at *; omega)), f₁ a (fun e he => by
      have := (show ∀ e ∈ zrowList, ZB ≤ e.2 ∧ e.2 + 64 ≤ 6080 by decide +kernel) e he
      omega)]
  refine ⟨fun h hh => ?_, fun sel hsel i hi => ?_, fun h hh => ?_, frame, fun h hh r hr k hk => ?_,
    by rw [g, g₃]; exact g₁, by rw [rd, rd₃]; exact rd₁, by rw [wr, wr₃]; exact wr₁, by rw [sy, sy₃]; exact sy₁⟩
  · refine hk.of_rows fun x h1 h2 => ?_
    show hmem b h t.mem (b + BitVec.ofNat 64 x) = _
    simp only [hmem]
    rw [off_ofNat _ (by omega)]
    by_cases hw : InWin x
    · rw [ite_eq_left hw]
      unfold InWin at hw
      -- the row of `x` among the window's constants
      obtain ⟨e, he, h3, h4, h5⟩ : ∃ e ∈ zrowList, e.1 ≤ x ∧ x < e.1 + 32 ∧ e.2 = zrow e.1 := by
        have : ∀ x, 1664 ≤ x → x < 1792 → ∃ e ∈ zrowList, e.1 ≤ x ∧ x < e.1 + 32 ∧ e.2 = zrow e.1 := by
          intro x h1 h2
          rcases (by omega : x < 1696 ∨ (1696 ≤ x ∧ x < 1728) ∨ (1728 ≤ x ∧ x < 1760) ∨ 1760 ≤ x) with h | h | h | h
          · exact ⟨(KM, zrow KM), by decide +kernel, by simp only [KM]; omega, by simp only [KM]; omega, rfl⟩
          · exact ⟨(K19, zrow K19), by decide +kernel, by simp only [K19]; omega, by simp only [K19]; omega, rfl⟩
          · exact ⟨(KB0, zrow KB0), by decide +kernel, by simp only [KB0]; omega, by simp only [KB0]; omega, rfl⟩
          · exact ⟨(KB1, zrow KB1), by decide +kernel, by simp only [KB1]; omega, by simp only [KB1]; omega, rfl⟩
        exact this x h1 (by omega)
      have hrow := (show ∀ e ∈ zrowList, 1024 ≤ e.1 → (e.1 - 1024) % 32 = 0 by decide +kernel) e he
      have := row e he (32 * h + (x - e.1)) (by omega)
      rw [h5] at this
      rw [show zoff h x = zrow e.1 + (32 * h + (x - e.1)) by
          have := hrow (by omega); unfold zoff zrow; omega, this]
      congr 3; omega
    · rw [ite_eq_right hw, frame _ (by simp only [ofs]; rw [off_ofNat _ (by omega)]; unfold ZB; omega)]
  · obtain ⟨k, hk4, e1, e2⟩ : ∃ k < 4, blendSels.getD k 0 = sel ∧ maskRow sel = ZMASK + 64 * k := by
      have : ∀ sel ∈ blendSels, ∃ k < 4, blendSels.getD k 0 = sel ∧ maskRow sel = ZMASK + 64 * k := by decide +kernel
      exact this sel hsel
    rw [m, e2, ← e1]
    exact c₃ k hk4 i hi
  · have w : ∀ d, d + 8 ≤ 32 → t.mem.readW (b + BitVec.ofNat 64 (ZK2 + 32 * h + d)) 64 =
        s.mem.readW (b + BitVec.ofNat 64 (offset 15 + d)) 64 := fun d hd =>
      readW_congr2 fun i hi => by
        rw [Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat]
        have := row (offset 15, ZK2) (by decide +kernel) (32 * h + d + i) (by omega)
        rw [show ZK2 + 32 * h + d + i = ZK2 + (32 * h + d + i) by omega, this]
        congr 3; omega
    have w0 := w 0 (by decide)
    simp only [Nat.add_zero] at w0
    simp only [VG.Proof.X25519.X86_64.F, VG.Proof.X25519.X86_64.fe, VG.Proof.X25519.X86_64.word, off]
    rw [w0, w 8 (by decide), w 16 (by decide), w 24 (by decide)]
  · have hn : ∀ r < 5, y r ≠ y 9 ∧ y r ≠ y 10 ∧ y r ≠ y 11 := by decide
    obtain ⟨n9, n10, n11⟩ := hn r hr
    rw [qw_half b t _ hk]
    simp only [zq]
    rw [← y_xr r (by omega), c r hr _ (by omega), show (2 * h + k / 2) % 2 = k / 2 by omega,
      z₃ _ n9 _ (by omega), zl₂ _ n10 n11 _ (by omega), z₁ _ n9 _ (by omega)]
    simp only [qw, State.zlane, show k / 2 < 2 by omega, ite_true]

end VG.Proof.Ed25519.X86_64.Zmm
