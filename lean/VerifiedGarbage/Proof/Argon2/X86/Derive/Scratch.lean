import VerifiedGarbage.Proof.Argon2.X86.Derive.Body

section

section

/-!
# Argon2 on x86 (32-bit): the derivation's locals

`lw s₀ s d`: the word at `[ebp + d]` in the body. A store to the locals keeps
the invariant and every other word (`Inv.store_loc`); writes to the memory
matrix, `scratch`, the output or the stack below the locals keep all of them
(`lw_keep`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd)
open VG.Spec.Blake2 (bytesAt)

/-- The word at `[ebp + d]`. -/
abbrev lw (s₀ s : State) (d : Nat) : BitVec 32 := s.mem.readW (addr (E s₀) d) 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem loc_addr {d : Nat} (hd : d < 236) :
    (E s₀ + BitVec.ofNat 32 d).toNat = (E s₀).toNat + d := add_nat (by have := E_hi hp; omega)

/-- Another word of the frame, after a store to the locals. -/
theorem lw_store {m : Mem} {d e : Nat} (hd : d + 4 ≤ 236) (he : e + 4 ≤ 236) (hde : d + 4 ≤ e ∨ e + 4 ≤ d)
    (v : BitVec 32) :
    (m.writeW (addr (E s₀) d) v).readW (addr (E s₀) e) 32 = m.readW (addr (E s₀) e) 32 :=
  Proof.Sha256.X86.Stream.readW_writeW_addr m v (by have := E_hi hp; omega) (by have := E_hi hp; omega) hde.symm

theorem Inv.store_loc {s t : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {v : BitVec 32}
    (u : Mupd s t (s.mem.writeW (addr (E s₀) d) v)) :
    Inv s₀ t ∧ lw s₀ t d = v ∧ ∀ e, e + 4 ≤ 236 → (d + 4 ≤ e ∨ e + 4 ≤ d) → lw s₀ t e = lw s₀ s e := by
  have hE := E_hi hp
  refine ⟨h.step (by rw [u.gpr]) (by rw [u.gpr]) u.rd u.wr ?_, ?_, fun e he hde => ?_⟩
  · rw [u.mem]
    exact (Frame.refl _ _).writeW (r := locR s₀) (by simp) v
      (contains32 (by rw [loc_addr hp (by omega)]; omega) (by rw [loc_addr hp (by omega)]; omega))
  · show t.mem.readW _ 32 = v
    rw [u.mem, Mem.readW_writeW_self32]
  · show t.mem.readW _ 32 = _
    rw [u.mem, lw_store hp (by omega) he hde]

/-- `mov [ebp + d], r` -/
theorem wp_stloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t d = s.gpr r → (∀ e, e + 4 ≤ 236 → (d + 4 ≤ e ∨ e + 4 ≤ d) →
      lw s₀ t e = lw s₀ s e) → t.gpr = s.gpr → t.mem = s.mem.writeW (addr (E s₀) d) (s.gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (.store ⟨.ebp, d⟩ r :: is)) s Q :=
  VG.X86.Wp.wp_stm h.ebp (loc_in hp h hd) fun t u =>
    let ⟨i, v, o⟩ := h.store_loc hp hd u
    k t i v o u.gpr u.mem

/-- `mov r, [ebp + d]` -/
theorem wp_ldloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (lw s₀ s d) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem ⟨.ebp, d⟩) :: is)) s Q :=
  VG.X86.Wp.wp_ldm h.ebp (loc_in' hp h hd) k

/-- `mov r, [ebp + argOff i]` -/
theorem wp_ldarg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem ⟨.ebp, Impl.Argon2.X86.Derive.argOff i⟩) :: is)) s Q :=
  VG.X86.Wp.wp_ldm h.ebp (h.arg_in hp hi) fun t u => k t (by rw [h.arg hp hi] at u; exact u)

/-- The locals are outside the memory matrix, `scratch`, the output and the stack below them. -/
theorem loc_disj {d : Nat} (hd : d + 4 ≤ 144) :
    ∀ r ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Disjoint ⟨addr (E s₀) d, 4⟩ r := by
  have hE := E_hi hp
  have hl := hp.esp_lo
  have hEn := E_nat hp
  have sub := loc_stk hp (d := d) (n := 4) hd
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact disj32 (.inr (by rw [sub_nat (by rw [E_nat hp]; omega), loc_addr hp (by omega)]; omega))
      (by rw [loc_addr hp (by omega)]; omega) (by rw [sub_nat (by rw [E_nat hp]; omega)]; omega)

/-- The locals are kept by writes outside them. -/
theorem lw_keep {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r') {d : Nat}
    (hd : d + 4 ≤ 144) : lw s₀ t d = lw s₀ s d :=
  (f.sub hs).readW (Region.contains_self _ _) (loc_disj hp hd) (by decide)

end

/-- The body's first instruction points `ebp` to the locals. -/
theorem inv_start {s₀ : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = (entry s₀).mem → (∀ r, r ≠ .ebp → t.gpr r = (entry s₀).gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (.mov .ebp (.reg .esp) :: is)) (entry s₀) Q :=
  VG.X86.Wp.wp_mov fun t u => k t
    ⟨by rw [u.other _ (by decide), entry_esp], by rw [u.gpr, entry_esp], by rw [u.rd, entry_rd],
      by rw [u.wr], by rw [u.mem]; exact Frame.refl _ _⟩ u.mem u.other

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the parameters

`parameters_ok`: the body's first instructions point `ebp` to the locals and
store there `4 · lanes` (the divisor), the segment length (by the fixed-time
division), the lane length and its size in bytes (`Prm`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd wp_add wp_addi wp_movi wp_mov)
open VG.Impl.Argon2.X86.Derive (parameters divisorOff segLenOff laneLenOff strideOff argOff)

/-- The parameters in the locals. -/
structure Prm (s₀ s : State) : Prop where
  divisor : lw s₀ s divisorOff = BitVec.ofNat 32 (4 * lanesN s₀)
  segLen : lw s₀ s segLenOff = BitVec.ofNat 32 (prm s₀).segmentLen
  laneLen : lw s₀ s laneLenOff = BitVec.ofNat 32 (prm s₀).laneLen
  stride : lw s₀ s strideOff = BitVec.ofNat 32 ((prm s₀).laneLen * 1024)

/-- `add ecx, ecx`, `n` times. -/
theorem dbl_ok {s : State} {is : List Instr} {Q : State → Prop} :
    ∀ n, (s.gpr .ecx).toNat * 2 ^ n < 2 ^ 32 →
      (∀ t, (t.gpr .ecx).toNat = (s.gpr .ecx).toNat * 2 ^ n → Divide.Keep s t → WP isa (.block is) t Q) →
      WP isa (.block (List.replicate n (.alu .add .ecx (.reg .ecx)) ++ is)) s Q
  | 0, _, k => k s (by simp) (Divide.Keep.refl s)
  | n + 1, hn, k => by
    rw [List.replicate_succ, List.cons_append]
    have e : (s.gpr .ecx).toNat * 2 ^ (n + 1) = (s.gpr .ecx).toNat * 2 * 2 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
    have hx : (s.gpr .ecx).toNat ≤ (s.gpr .ecx).toNat * 2 ^ n :=
      Nat.le_mul_of_pos_right _ (Nat.two_pow_pos n)
    have two : (s.gpr .ecx).toNat * 2 < 2 ^ 32 := by
      have := Nat.mul_le_mul_right 2 hx
      rw [Nat.mul_right_comm] at this
      rw [e] at hn
      omega
    refine wp_add fun s₁ u₁ _ => dbl_ok (s := s₁) n ?_ fun t ht kt => k t ?_
      ((Divide.Keep.of_upd u₁ (by simp)).trans kt)
    · rw [u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), ← Nat.two_mul, Nat.mul_comm 2]
      rw [e] at hn; exact hn
    · rw [ht, u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), ← Nat.two_mul, Nat.mul_comm 2, e]

theorem lw_mem {s₀ s t : State} (h : t.mem = s.mem) (d : Nat) : lw s₀ t d = lw s₀ s d := by
  simp only [lw, h]

theorem Inv.keep {s₀ s t : State} (h : Inv s₀ s) (k : Divide.Keep s t) : Inv s₀ t :=
  h.step (k.other _ (by decide) (by decide) (by decide)) (k.other _ (by decide) (by decide) (by decide))
    k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem parameters_ok {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → Prm s₀ t → WP isa (.block is) t Q) :
    WP isa (.block ((.mov .ebp (.reg .esp) :: parameters) ++ is)) (entry s₀) Q := by
  have hL := hp.lanes_lt
  have hL1 := hp.lanes_pos
  have hBl := hp.blocks_lt
  have hb := hp.blocks_eq
  have hseg := hp.segLen_eq
  have hlane := hp.laneLen_eq
  simp only [parameters, Impl.Argon2.X86.Derive.fr, List.cons_append, List.append_assoc]
  refine inv_start fun s₁ i₁ _ _ => ?_
  refine wp_ldarg hp i₁ (i := Impl.Argon2.X86.Derive.lanesArg) (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide) (by decide)
  refine wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ => ?_
  have i₄ := (i₂.upd u₃ (by decide) (by decide)).upd u₄ (by decide) (by decide)
  have e₄ : (s₄.gpr .eax).toNat = 4 * lanesN s₀ := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr]
    simp only [BitVec.toNat_add]
    show (((arg s₀ 7).toNat + (arg s₀ 7).toNat) % 2 ^ 32 + ((arg s₀ 7).toNat + (arg s₀ 7).toNat) % 2 ^ 32)
      % 2 ^ 32 = 4 * (arg s₀ 7).toNat
    have : (arg s₀ 7).toNat < 2 ^ 24 := hL
    omega
  refine wp_stloc hp i₄ (d := divisorOff) (by decide) fun s₅ i₅ v₅ _ g₅ _ => ?_
  refine wp_ldarg hp i₅ (i := Impl.Argon2.X86.Derive.memoryCostArg) (by decide) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆ (by decide) (by decide)
  have d₆ : lw s₀ s₆ divisorOff = s₄.gpr .eax := by rw [lw_mem u₆.mem, v₅]
  refine Divide.code_ok (D := s₄.gpr .eax) (by rw [e₄]; omega) (by rw [e₄]; omega) i₆.ebp
    (loc_in' hp i₆ (by decide)) d₆ fun s₇ c₇ _ k₇ => ?_
  have i₇ := i₆.keep k₇
  rw [u₆.gpr, e₄] at c₇
  have c₇' : (s₇.gpr .ecx).toNat = (prm s₀).segmentLen := by rw [c₇, hseg]; rfl
  refine wp_stloc hp i₇ (d := segLenOff) (by decide) fun s₈ i₈ v₈ o₈ g₈ _ => ?_
  have hll : (prm s₀).laneLen ≤ blocksN s₀ :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ hL1) (Nat.le_of_eq hb.symm)
  have hsegL : (prm s₀).laneLen * 1024 + 16384 ≤ 2 ^ 32 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right 1024 hll) _) hBl
  refine wp_add fun s₉ u₉ _ => wp_add fun s₁₀ u₁₀ _ => ?_
  have i₁₀ := (i₈.upd u₉ (by decide) (by decide)).upd u₁₀ (by decide) (by decide)
  have e₁₀ : (s₁₀.gpr .ecx).toNat = (prm s₀).laneLen := by
    rw [u₁₀.gpr, u₉.gpr, g₈]
    simp only [BitVec.toNat_add, c₇']
    omega
  refine wp_stloc hp i₁₀ (d := laneLenOff) (by decide) fun s₁₁ i₁₁ v₁₁ o₁₁ g₁₁ _ => ?_
  refine dbl_ok 10 (by rw [g₁₁, e₁₀]; omega) fun s₁₂ e₁₂ k₁₂ => ?_
  have i₁₂ := i₁₁.keep k₁₂
  refine wp_stloc hp i₁₂ (d := strideOff) (by decide) fun s₁₃ i₁₃ v₁₃ o₁₃ _ _ => k s₁₃ i₁₃ ⟨?_, ?_, ?_, ?_⟩
  · rw [o₁₃ _ (by decide) (by decide), lw_mem k₁₂.mem, o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem,
      lw_mem u₉.mem, o₈ _ (by decide) (by decide), lw_mem k₇.mem, lw_mem u₆.mem, v₅]
    exact BitVec.eq_of_toNat_eq (by rw [e₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [o₁₃ _ (by decide) (by decide), lw_mem k₁₂.mem, o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem,
      lw_mem u₉.mem, v₈]
    exact BitVec.eq_of_toNat_eq (by rw [c₇', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [o₁₃ _ (by decide) (by decide), lw_mem k₁₂.mem, v₁₁]
    exact BitVec.eq_of_toNat_eq (by rw [e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [v₁₃]
    exact BitVec.eq_of_toNat_eq (by
      rw [e₁₂, g₁₁, e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])

end

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the derivation's use of H′'s hash macros

The H₀ code calls the BLAKE2b functions through H′'s macros
(`Impl.Argon2.X86.HPrime`), with `ebx` pointing to `scratch` and the stack
below the locals: `ctx` gives their context (`HPrime.Ctx`), and `Inv.keeps`
the body's invariant and locals after them. `Inv.store_scr` is a store to
`scratch` through `ebx`.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd)
open VG.Proof.Argon2.X86.HPrime (Ctx Keeps)

/-- `n` bytes of `scratch` at offset `d`. -/
theorem scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 16384) :
    Region.Sub ⟨(scrP s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ (scrR s₀) := Offset.sub_base _ h

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_mem : scrR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)
theorem mem_mem : memR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)
theorem out_mem : outR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)


/-- The 60 bytes below the locals that H′'s macros use are outside the body's other regions. -/
theorem below60_call : Region.Sub (VG.X86.below (E s₀) 60) (callR s₀) :=
  VG.X86.below_sub (by decide) (by rw [E_nat hp]; have := hp.esp_lo; omega)

theorem ctx {s : State} (h : Inv s₀ s) (hb : s.gpr .ebx = scrP s₀) : Ctx (scrP s₀) (E s₀) s := by
  have := hp.scr_fits
  refine ⟨hb, h.esp, by omega, by rw [E_nat hp]; have := hp.esp_lo; omega,
    by have := E_hi hp; omega, ?_, ?_⟩
  · rw [h.wr]
    exact (Covers.of_sub (rs' := [scrR s₀]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact scr_mem hp, hc⟩)
  · exact ((hp.stk_all (scrR s₀) (by simp)).sub_left fun a ha => call_stk hp a (below60_call hp a ha)).sub_right
      (Region.sub_prefix (by decide))

/-- What H′'s macros keep keeps the body's invariant and the locals. -/
theorem Inv.keeps {s t : State} (h : Inv s₀ s) (k : Keeps (scrP s₀) (E s₀) s t) :
    Inv s₀ t ∧ ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d := by
  have sub : ∀ r ∈ [(⟨(scrP s₀).setWidth 64, 832⟩ : Region), VG.X86.below (E s₀) 60],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨callR s₀, by simp, below60_call hp⟩
  refine ⟨h.step k.esp k.ebp k.rd k.wr (k.frame.sub fun r hr => ?_), fun d hd => lw_keep hp k.frame sub hd⟩
  obtain ⟨r', hr', hs⟩ := sub r hr
  refine ⟨r', ?_, hs⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl <;> simp

end

/-! ## The hash macros, with `Keeps` -/

section
open VG.Spec.Blake2

variable {B E : BitVec 32} {s : State} (c : Ctx B E s)
include c

theorem init_k {n : Nat} (hn : s.gpr .edx = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa Impl.Argon2.X86.HPrime.init s fun t =>
      Repr b (Spec.Blake2.init b n 0) t.mem (B.setWidth 64) [] ∧ Keeps B E s t :=
  (HPrime.init_ok c hn hn₁ hn₂).mono fun t ⟨r, cs, rd, wr, f⟩ =>
    ⟨r, Keeps.of_call (HPrime.of_callee cs) rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) c.lo⟩⟩

theorem update_k {D : BitVec 32} {L : Nat}
    (hD : s.gpr .esi = D) (hL : (s.gpr .edi).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨D.setWidth 64, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨D.setWidth 64, L⟩ ⟨B.setWidth 64, 768⟩)
    (hDk : (below E 60).Disjoint ⟨D.setWidth 64, L⟩)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (B.setWidth 64) d)
    (hc : s.gpr .edx ++ s.gpr .ecx = BitVec.ofNat 64 d.length) (hlen : d.length + L < 2 ^ 64) :
    WP isa Impl.Argon2.X86.HPrime.update s fun t =>
      Repr b h0 t.mem (B.setWidth 64) (d ++ bytesAt s.mem (D.setWidth 64) L) ∧ Keeps B E s t :=
  (HPrime.update_ok c hD hL hDfit hDc hDs hDk repr hc hlen).mono fun t ⟨r, cs, rd, wr, f⟩ =>
    ⟨r, Keeps.of_call (HPrime.of_callee cs) rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩⟩

theorem finalize_k {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (B.setWidth 64) d)
    (hc : s.gpr .edx ++ s.gpr .ecx = BitVec.ofNat 64 d.length) (hlen : d.length < 2 ^ 64) :
    WP isa Impl.Argon2.X86.HPrime.finalize s fun t =>
      bytesAt t.mem (B.setWidth 64 + 768) 64 = finalHash b h0 d ∧ Keeps B E s t :=
  (HPrime.finalize_ok c repr hc hlen).mono fun t ⟨dg, cs, rd, wr, f⟩ =>
    ⟨dg, Keeps.of_call (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact cs _ (by decide) (by decide)) rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩⟩

end

end VG.Proof.Argon2.X86.Derive
