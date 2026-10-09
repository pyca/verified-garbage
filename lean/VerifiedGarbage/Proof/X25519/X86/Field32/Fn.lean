import VerifiedGarbage.Proof.X25519.X86.Field32.Copy
import VerifiedGarbage.TCB.X86.Target

/-!
# `vg_gf25519_r32_mul` on x86 (32-bit): what it computes

From its entry (`Entry`: the working space `ws` at `x`, its arguments on
the stack apart from it), `entry` saves `ebx`, `ebp` and `edi` at `SAVE`
and points `edi`, `ecx` and `edx` at the working space and the operands
(`entry_ok`); the body copies the operands to `opA` (and `opB`) and runs
X25519's product into `opA` (`sqrBody_ok`, `mulBody_ok`); `exit` restores
the registers and copies the result to `[o]` (`exit_ok`). `mulFn_ok`: the
function keeps `ebx`, `esi`, `edi`, `ebp` and `esp`, changes memory only
in `[o]` and its own working space, and leaves at `[o]` a number congruent
to the product of `[a]` and `[b]` modulo `p`.
-/

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86 VG.Spec.X25519

/-- The function's entry: the working space `ws = x` (its first argument),
writable for 4096 bytes and within the 32-bit address space; the four
arguments readable and apart from it, as is the return address; the offsets
`o`, `a` and `b` below the function's own working space. -/
structure Entry (s : State) (x : BitVec 32) (o a b : Nat) : Prop where
  ws : arg s 0 = x
  fit : x.toNat + 4096 ≤ 2 ^ 32
  wr : scR 4096 x ∈ s.wr
  read : ∀ i < 4, InRegions (s.rd ++ s.wr) (argAddr s i) 4
  out : ∀ i < 4, (⟨argAddr s i, 4⟩ : Region).Disjoint (scR 4096 x)
  ret : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (scR 4096 x)
  argO : arg s 1 = BitVec.ofNat 32 o
  argA : arg s 2 = BitVec.ofNat 32 a
  argB : arg s 3 = BitVec.ofNat 32 b
  ho : o + 32 ≤ 768
  ha : a + 32 ≤ 768
  hb : b + 32 ≤ 768

/-- A region of the working space. -/
theorem sub_ws {x : BitVec 32} (hx : x.toNat + 4096 ≤ 2 ^ 32) {d n : Nat} (h : d + n ≤ 4096) (hn : 0 < n) :
    Region.Sub (sub x d n) (scR 4096 x) := by
  rw [scR_eq]
  exact sub_sub hx (Nat.zero_le _) (by omega) (by omega)

/-- A frame within the working space keeps the words apart from it. -/
theorem frame_out {x : BitVec 32} {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m') (hs : ∀ r ∈ rs, Region.Sub r (scR 4096 x)) {a : Addr}
    (ha : (⟨a, 4⟩ : Region).Disjoint (scR 4096 x)) : m'.readW a 32 = m.readW a 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => ha.sub_right (hs r hr)) (by decide)

/-- What the state after `entry` keeps: the counter `esi`, `esp`, the regions. -/
structure EKeep (s t : State) : Prop where
  esi : t.gpr .esi = s.gpr .esi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem argAddr_eq {s t : State} (h : t.gpr .esp = s.gpr .esp) (i : Nat) : argAddr t i = argAddr s i := by
  simp only [argAddr, h]

/-- Argument `i`, through a frame within the working space. -/
theorem arg_frame {s t : State} {x : BitVec 32} {o a b : Nat} (h : Entry s x o a b) (hsp : t.gpr .esp = s.gpr .esp)
    {rs : List Region} (hf : Frame rs s.mem t.mem) (hs : ∀ r ∈ rs, Region.Sub r (scR 4096 x)) {i : Nat}
    (hi : i < 4) : arg t i = arg s i := by
  simp only [arg, argAddr_eq hsp]
  exact frame_out hf hs (h.out i hi)

/-- The registers saved at `SAVE`. -/
structure Saved (x : BitVec 32) (g : Reg → BitVec 32) (m : Mem) : Prop where
  ebx : wd m x SAVE = g .ebx
  ebp : wd m x (SAVE + 4) = g .ebp
  edi : wd m x (SAVE + 8) = g .edi

theorem add_ofNat_eq {x : BitVec 32} {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (x + BitVec.ofNat 32 a - (x + BitVec.ofNat 32 b) == 0) = decide (a = b) := by
  rw [show x + BitVec.ofNat 32 a - (x + BitVec.ofNat 32 b) = BitVec.ofNat 32 a - BitVec.ofNat 32 b by
    bv_omega]
  by_cases e : a = b
  · subst e; simp
  · have hne : BitVec.ofNat 32 a ≠ BitVec.ofNat 32 b := fun h' => e (by
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)
    simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
    exact fun h' => hne (by bv_omega)

theorem entry_ok {s : State} {x : BitVec 32} {o a b : Nat} (h : Entry s x o a b) :
    WP isa (.block entry) s fun t =>
      Ctx 4096 x t ∧ t.gpr .ecx = x + BitVec.ofNat 32 a ∧ t.gpr .edx = x + BitVec.ofNat 32 b ∧
      t.zf = some (decide (a = b)) ∧ EKeep s t ∧ Frame [sub x SAVE 12] s.mem t.mem ∧ Saved x s.gpr t.mem := by
  have hfit := h.fit
  have hS : SAVE + 12 ≤ 4096 := by decide
  refine Wp.wp_ldm (b := .esp) (o := 4 + 4 * 0) rfl (h.read 0 (by decide)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = x := by rw [u₁.gpr]; exact h.ws
  refine Wp.wp_stm e₁ ⟨_, by rw [u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₂ u₂ => ?_
  refine Wp.wp_stm (by rw [u₂.gpr]; exact e₁)
    ⟨_, by rw [u₂.wr, u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₃ u₃ => ?_
  refine Wp.wp_stm (by rw [u₃.gpr, u₂.gpr]; exact e₁)
    ⟨_, by rw [u₃.wr, u₂.wr, u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₄ u₄ => ?_
  refine Wp.wp_mov fun s₅ u₅ => ?_
  -- The memory now: the three saves.
  have m₅ : s₅.mem = ((s.mem.writeW (addr x SAVE) (s.gpr .ebx)).writeW (addr x (SAVE + 4)) (s.gpr .ebp)).writeW
      (addr x (SAVE + 8)) (s.gpr .edi) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.other .edi (by decide),
      u₁.other .ebp (by decide), u₁.other .ebx (by decide)]
  have f₅ : Frame [sub x SAVE 12] s.mem s₅.mem := by
    rw [m₅]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
      |>.writeW (List.mem_singleton_self _) _ ?_ <;>
    exact sub_contains (by simp only [SAVE]; omega_using [hfit]) (by decide) (by decide) (by decide)
  have hs₅ : ∀ r ∈ [sub x SAVE 12], Region.Sub r (scR 4096 x) := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact sub_ws hfit hS (by decide)
  have sp₅ : s₅.gpr .esp = s.gpr .esp := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have edi₅ : s₅.gpr .edi = x := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁
  have rdA : ∀ i < 4, InRegions (s₅.rd ++ s₅.wr) (addr (s₅.gpr .esp) (4 + 4 * i)) 4 := fun i hi => by
    rw [rd₅, wr₅, sp₅]; exact h.read i hi
  have argv : ∀ i < 4, s₅.mem.readW (addr (s₅.gpr .esp) (4 + 4 * i)) 32 = arg s i := fun i hi => by
    rw [sp₅]; exact frame_out f₅ hs₅ (h.out i hi)
  refine Wp.wp_ldm (b := .esp) (o := 4 + 4 * 2) rfl (rdA 2 (by decide)) fun s₆ u₆ => ?_
  refine Wp.wp_ldm (b := .esp) (o := 4 + 4 * 3) (by rw [u₆.other _ (by decide)])
    (by rw [u₆.rd, u₆.wr]; exact rdA 3 (by decide)) fun s₇ u₇ => ?_
  refine Wp.wp_add fun s₈ u₈ _ => Wp.wp_add fun s₉ u₉ _ => Wp.wp_cmp fun s₁₀ u₁₀ _ z₁₀ => WP.block_nil ?_
  rw [u₆.mem] at u₇
  have ecx₉ : s₉.gpr .ecx = x + BitVec.ofNat 32 a := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.gpr, argv 2 (by decide), h.argA,
      u₇.other _ (by decide), u₆.other _ (by decide), edi₅, BitVec.add_comm]
  have edx₉ : s₉.gpr .edx = x + BitVec.ofNat 32 b := by
    rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, argv 3 (by decide), h.argB, u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), edi₅, BitVec.add_comm]
  have edi₉ : s₉.gpr .edi = x := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), edi₅]
  have mem₁₀ : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have k₁₀ : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .eax → r ≠ .edi → s₁₀.gpr r = s.gpr r := by
    intro r h1 h2 h3 h4
    rw [u₁₀.gpr, u₉.other _ h2, u₈.other _ h1, u₇.other _ h2, u₆.other _ h1, u₅.other _ h4, u₄.gpr, u₃.gpr,
      u₂.gpr, u₁.other _ h3]
  refine ⟨⟨by rw [u₁₀.gpr]; exact edi₉, hfit, by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]; exact h.wr,
    by decide, fun _ hW => absurd hW (by decide)⟩, by rw [u₁₀.gpr]; exact ecx₉, by rw [u₁₀.gpr]; exact edx₉, ?_, ?_, by rw [mem₁₀]; exact f₅, ?_⟩
  · rw [z₁₀, ecx₉, edx₉, add_ofNat_eq (by omega_using [h.ha]) (by omega_using [h.hb])]
  · exact ⟨k₁₀ _ (by decide) (by decide) (by decide) (by decide), k₁₀ _ (by decide) (by decide) (by decide) (by decide),
      by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅], by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]⟩
  · rw [mem₁₀, m₅]
    refine ⟨?_, ?_, ?_⟩
    · rw [wd_write_ne _ _ (by simp only [SAVE]; omega_using [hfit]) (by simp only [SAVE]; omega_using [hfit])
        (by decide),
        wd_write_ne _ _ (by simp only [SAVE]; omega_using [hfit]) (by simp only [SAVE]; omega_using [hfit])
        (by decide), wd_write_self]
    · rw [wd_write_ne _ _ (by simp only [SAVE]; omega_using [hfit]) (by simp only [SAVE]; omega_using [hfit])
        (by decide), wd_write_self]
    · rw [wd_write_self]

/-- A frame of regions within `R` is one of `R`. -/
theorem frame_into {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hs : ∀ r ∈ rs, Region.Sub r R) : Frame [R] m m' :=
  hf.sub fun r hr => ⟨R, List.mem_singleton_self _, hs r hr⟩

/-- The body's frame: the copies, and X25519's product. -/
abbrev bodyW (x : BitVec 32) : List Region := [sub x opA 64, sub x T 64]

/-- What a transfer keeps, as the field arithmetic states it. -/
theorem XKeep.keep {s t : State} (h : XKeep s t) : Keep s t :=
  ⟨h.gpr _ (by decide), h.gpr _ (by decide), h.gpr _ (by decide), h.rd, h.wr⟩

theorem below_opA : Below opA := by decide
theorem below_opB : Below opB := by decide

theorem sqrBody_ok {t : State} {x : BitVec 32} {a : Nat} (hc : Ctx 4096 x t) (ha : a + 32 ≤ 768)
    (hecx : t.gpr .ecx = x + BitVec.ofNat 32 a) :
    WP isa (.block sqrBody) t fun u => Ctx 4096 x u ∧ Keep t u ∧ Frame (bodyW x) t.mem u.mem ∧
      fe u.mem x opA % P = fe t.mem x a * fe t.mem x a % P := by
  have hfit := hc.fit
  rw [sqrBody, copyIn_eq, WP.block_append_iff]
  refine WP.mono (xfer8_ok (W := 4096) (a := a) (o := opA) ⟨hfit, hc.wr, hecx,
    by rw [hc.edi]; exact (BitVec.add_zero x).symm, by decide, by decide, fun _ _ => rfl,
    fun _ _ => Nat.zero_add _, by omega_using [ha], by decide, .inl (by simp only [opA]; omega_using [ha])⟩)
    fun u₁ ⟨k₁, f₁, v₁⟩ => ?_
  have c₁ := k₁.keep.ctx hc
  refine WP.mono (mul_ok c₁ below_opA below_opA below_opA) fun u₂ ⟨k₂, f₂, v₂⟩ => ?_
  refine ⟨k₂.ctx c₁, k₁.keep.trans k₂, ?_, by rw [v₂, v₁]⟩
  refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_cons_self .., sub_sub hfit (Nat.le_refl _) (by decide) (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_sub hfit (Nat.le_refl _) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), sub_sub hfit (Nat.le_refl _) (by decide)
        (by decide)⟩

theorem mulBody_ok {t : State} {x : BitVec 32} {a b : Nat} (hc : Ctx 4096 x t) (ha : a + 32 ≤ 768)
    (hb : b + 32 ≤ 768) (hecx : t.gpr .ecx = x + BitVec.ofNat 32 a) (hedx : t.gpr .edx = x + BitVec.ofNat 32 b) :
    WP isa (.block mulBody) t fun u => Ctx 4096 x u ∧ Keep t u ∧ Frame (bodyW x) t.mem u.mem ∧
      fe u.mem x opA % P = fe t.mem x a * fe t.mem x b % P := by
  have hfit := hc.fit
  rw [mulBody, copyIn_eq, copyIn_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (xfer8_ok (W := 4096) (a := a) (o := opA) ⟨hfit, hc.wr, hecx,
    by rw [hc.edi]; exact (BitVec.add_zero x).symm, by decide, by decide, fun _ _ => rfl,
    fun _ _ => Nat.zero_add _, by omega_using [ha], by decide, .inl (by simp only [opA]; omega_using [ha])⟩)
    fun u₁ ⟨k₁, f₁, v₁⟩ => ?_
  have c₁ := k₁.keep.ctx hc
  refine WP.mono (xfer8_ok (W := 4096) (a := b) (o := opB) ⟨hfit, c₁.wr,
    by rw [k₁.gpr _ (by decide)]; exact hedx, by rw [c₁.edi]; exact (BitVec.add_zero x).symm, by decide,
    by decide, fun _ _ => rfl, fun _ _ => Nat.zero_add _, by omega_using [hb], by decide,
    .inl (by simp only [opB]; omega_using [hb])⟩)
    fun u₂ ⟨k₂, f₂, v₂⟩ => ?_
  have c₂ := k₂.keep.ctx c₁
  refine WP.mono (mul_ok c₂ below_opA below_opA below_opB) fun u₃ ⟨k₃, f₃, v₃⟩ => ?_
  have e₁ : fe u₁.mem x b = fe t.mem x b :=
    fe_frame1 f₁ hfit (by decide) (by omega_using [hb]) (.inl (by simp only [opA]; omega_using [hb]))
  have e₂ : fe u₂.mem x opA = fe u₁.mem x opA :=
    fe_frame1 f₂ hfit (by decide) (by decide) (.inl (by decide))
  refine ⟨k₃.ctx c₂, k₁.keep.trans (k₂.keep.trans k₃), ?_, by rw [v₃, e₂, v₁, v₂, e₁]⟩
  refine (f₁.sub fun r hr => ?_).trans ((f₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_))
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_cons_self .., sub_sub hfit (Nat.le_refl _) (by decide) (by decide)⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_cons_self .., sub_sub hfit (by decide) (by decide) (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_sub hfit (Nat.le_refl _) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), sub_sub hfit (Nat.le_refl _) (by decide)
        (by decide)⟩

theorem exit_ok {u : State} {x : BitVec 32} {o : Nat} {g : Reg → BitVec 32} (hc : Ctx 4096 x u)
    (ho : o + 32 ≤ 768) (hrd : InRegions (u.rd ++ u.wr) (argAddr u 1) 4) (hargo : arg u 1 = BitVec.ofNat 32 o)
    (hsv : Saved x g u.mem) :
    WP isa (.block exit) u fun v => v.gpr .ebx = g .ebx ∧ v.gpr .ebp = g .ebp ∧ v.gpr .edi = g .edi ∧
      v.gpr .esi = u.gpr .esi ∧ v.gpr .esp = u.gpr .esp ∧ v.rd = u.rd ∧ v.wr = u.wr ∧
      Frame [sub x o 32] u.mem v.mem ∧ fe v.mem x o = fe u.mem x opA := by
  have hfit := hc.fit
  rw [exit, WP.block_append_iff]
  refine Wp.wp_mov fun u₁ v₁ => ?_
  refine Wp.wp_ldm (b := .esp) (o := 4 + 4 * 1) rfl (by rw [v₁.rd, v₁.wr, v₁.other _ (by decide)]; exact hrd)
    fun u₂ v₂ => ?_
  refine Wp.wp_add fun u₃ v₃ _ => ?_
  have edx₃ : u₃.gpr .edx = x := by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, hc.edi]
  have m₃ : u₃.mem = u.mem := by rw [v₃.mem, v₂.mem, v₁.mem]
  have wr₃ : u₃.wr = u.wr := by rw [v₃.wr, v₂.wr, v₁.wr]
  have rin : ∀ d, d + 4 ≤ 4096 → InRegions (u₃.rd ++ u₃.wr) (addr x d) 4 := fun d hd =>
    ⟨_, List.mem_append_right _ (by rw [wr₃]; exact hc.wr), scR_contains hfit hd (by decide)⟩
  refine Wp.wp_ldm (B := x) (o := SAVE) edx₃ (rin _ (by decide)) fun u₄ v₄ => ?_
  refine Wp.wp_ldm (B := x) (o := SAVE + 4) (by rw [v₄.other _ (by decide)]; exact edx₃)
    (by rw [v₄.rd, v₄.wr]; exact rin _ (by decide)) fun u₅ v₅ => ?_
  refine Wp.wp_ldm (B := x) (o := SAVE + 8) (by rw [v₅.other _ (by decide), v₄.other _ (by decide)]; exact edx₃)
    (by rw [v₅.rd, v₅.wr, v₄.rd, v₄.wr]; exact rin _ (by decide)) fun u₆ v₆ => WP.block_nil ?_
  have ecx₆ : u₆.gpr .ecx = x + BitVec.ofNat 32 o := by
    rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.gpr,
      v₂.other _ (by decide), v₁.gpr, hc.edi, v₁.mem, v₁.other .esp (by decide)]
    rw [show u.mem.readW (addr (u.gpr .esp) (4 + 4 * 1)) 32 = arg u 1 from rfl, hargo, BitVec.add_comm]
  have edx₆ : u₆.gpr .edx = x + BitVec.ofNat 32 0 := by
    rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), edx₃]
    exact (BitVec.add_zero x).symm
  have m₆ : u₆.mem = u.mem := by rw [v₆.mem, v₅.mem, v₄.mem, m₃]
  have wr₆ : u₆.wr = u.wr := by rw [v₆.wr, v₅.wr, v₄.wr, wr₃]
  rw [copyOut_eq]
  refine WP.mono (xfer8_ok (W := 4096) (a := opA) (o := o) ⟨hfit, by rw [wr₆]; exact hc.wr, edx₆, ecx₆,
    by decide, by decide, fun _ _ => Nat.zero_add _, fun _ _ => rfl, by decide, by omega_using [ho],
    .inr (by simp only [opA]; omega_using [ho])⟩) fun v ⟨k, f, e⟩ => ?_
  rw [m₆] at f e
  refine ⟨?_, ?_, ?_, ?_, ?_, by rw [k.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd],
    by rw [k.wr, wr₆], f, e⟩
  · rw [k.gpr _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, m₃]; exact hsv.ebx
  · rw [k.gpr _ (by decide), v₆.other _ (by decide), v₅.gpr, v₄.mem, m₃]; exact hsv.ebp
  · rw [k.gpr _ (by decide), v₆.gpr, v₅.mem, v₄.mem, m₃]; exact hsv.edi
  · rw [k.gpr _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)]
  · rw [k.gpr _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)]

/-- The body keeps the saved registers. -/
theorem Saved.body {x : BitVec 32} (hfit : x.toNat + 4096 ≤ 2 ^ 32) {g : Reg → BitVec 32} {m m' : Mem}
    (h : Saved x g m) (hf : Frame (bodyW x) m m') : Saved x g m' := by
  have k : ∀ d, SAVE ≤ d → d + 4 ≤ T → wd m' x d = wd m x d := fun d h₁ h₂ =>
    wd_frame hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [SAVE, T] at h₁ h₂
      rcases hr with rfl | rfl
      · exact sub_disj (by omega_using [hfit, h₂]) (by simp only [opA]; omega_using [hfit])
          (.inr (by simp only [opA]; omega))
      · exact sub_disj (by omega_using [hfit, h₂]) (by simp only [T]; omega_using [hfit])
          (.inl (by simp only [T]; omega))
  exact ⟨(k _ (by decide) (by decide)).trans h.ebx, (k _ (by decide) (by decide)).trans h.ebp,
    (k _ (by decide) (by decide)).trans h.edi⟩

/-- The regions the function writes, within its working space. -/
theorem fnW_sub {x : BitVec 32} (hfit : x.toNat + 4096 ≤ 2 ^ 32) :
    ∀ r ∈ sub x SAVE 12 :: bodyW x, Region.Sub r (scR 4096 x) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact sub_ws hfit (by decide) (by decide)

theorem mulFn_ok {s : State} {x : BitVec 32} {o a b : Nat} (h : Entry s x o a b) :
    WP isa mulFn s fun t => (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [sub x o 32, sub x opA 256] s.mem t.mem ∧
      fe t.mem x o % P = fe s.mem x a * fe s.mem x b % P := by
  have hfit := h.fit
  refine WP.seq (WP.mono (entry_ok h) fun t ⟨hc, hecx, hedx, hz, hk, hf, hsv⟩ => ?_)
  have hbody : WP isa (.ite .e (.block sqrBody) (.block mulBody)) t fun u => Ctx 4096 x u ∧ Keep t u ∧
      Frame (bodyW x) t.mem u.mem ∧ fe u.mem x opA % P = fe t.mem x a * fe t.mem x b % P := by
    refine WP.ite (decide (a = b)) hz (fun hab => ?_) (fun _ => mulBody_ok hc h.ha h.hb hecx hedx)
    have e := of_decide_eq_true hab; subst e
    exact sqrBody_ok hc h.ha hecx
  refine WP.seq (WP.mono hbody fun u ⟨cu, ku, fu, vu⟩ => ?_)
  have fsu : Frame (sub x SAVE 12 :: bodyW x) s.mem u.mem :=
    (hf.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..).trans
      (fu.mono fun r hr => List.mem_cons_of_mem _ hr)
  have spu : u.gpr .esp = s.gpr .esp := ku.esp.trans hk.esp
  have hargo : arg u 1 = BitVec.ofNat 32 o := (arg_frame h spu fsu (fnW_sub hfit) (by decide)).trans h.argO
  have hrd : InRegions (u.rd ++ u.wr) (argAddr u 1) 4 := by
    rw [argAddr_eq spu, ku.rd, ku.wr, hk.rd, hk.wr]; exact h.read 1 (by decide)
  refine WP.mono (exit_ok cu h.ho hrd hargo (hsv.body hfit fu)) fun v ⟨rb, rp, ri, rs, re, rr, rw', fv, ev⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [rr, ku.rd, hk.rd], by rw [rw', ku.wr, hk.wr], ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rb
    · rw [rs, ku.esi, hk.esi]
    · exact ri
    · exact rp
    · rw [re, spu]
  · refine (fsu.sub fun r hr => ?_).trans (fv.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)
    refine ⟨sub x opA 256, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact sub_sub hfit (by decide) (by decide) (by decide)
  · have ea : fe t.mem x a = fe s.mem x a :=
      fe_frame1 hf hfit (by decide) (by omega_using [h.ha]) (.inl (by simp only [SAVE]; omega_using [h.ha]))
    have eb : fe t.mem x b = fe s.mem x b :=
      fe_frame1 hf hfit (by decide) (by omega_using [h.hb]) (.inl (by simp only [SAVE]; omega_using [h.hb]))
    rw [ev, vu, ea, eb]

end VG.Proof.X25519.X86.Field32
