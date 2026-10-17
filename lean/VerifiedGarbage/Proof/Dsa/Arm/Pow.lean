module

public import VerifiedGarbage.Impl.Dsa.Arm.Pow
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Exponent
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA's exponentiation as a function on 32-bit ARM: its code

`vg_dsa_pow_{n}_{e}` (`Impl/Dsa/Arm/Pow.lean`) saves the registers it uses
in the header (`stores_ok`), sets up the context and exponentiates, and
loads them back (`loads_ok`): `body_ok`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_str wp_ldr op2_reg)

/-- Words at the offsets `l` of the working space, four bytes apart. -/
def Apart (l : List (Reg × Nat)) : Prop := l.Pairwise fun a b => a.2 + 4 ≤ b.2 ∨ b.2 + 4 ≤ a.2

/-- The words `l` lists, each within an immediate offset of `r12` and the
working space. -/
def Fit (size : Nat) (l : List (Reg × Nat)) : Prop := ∀ x ∈ l, x.2 < 4096 ∧ x.2 + 4 ≤ size

/-- The ranges of the words. -/
def words (l : List (Reg × Nat)) : List (Nat × Nat) := l.map fun x => (x.2, 4)

/-- Stores of registers at offsets of `r12`, none of them `r12`. -/
theorem stores_ok {base : Addr} {size : Nat} :
    ∀ (l : List (Reg × Nat)) {s : State}, Ws s base size → Fit size l → Apart l →
      WP isa (.block (l.map fun (r, o) => .str r .r12 o)) s fun t =>
        (∀ x ∈ l, t.mem.readW (off base x.2) 32 = s.gpr x.1) ∧ Outs base (words l) s.mem t.mem ∧
        Rest [] s t
  | [], s, _, _, _ => WP.block_nil ⟨(fun _ h => nomatch h), Outs.refl _ _ _, Rest.refl _ _⟩
  | (r, o) :: l, s, hs, hf, ha => by
    have nw := hs.nowrap
    obtain ⟨ho, ho'⟩ := hf _ (List.mem_cons_self ..)
    refine wp_str ho (hs.ea12 (by omega)) (hs.write ho') fun s₁ m₁ => ?_
    have ha' := List.pairwise_cons.mp ha
    refine WP.mono (stores_ok l (hs.of_mupd m₁) (fun x hx => hf x (List.mem_cons_of_mem _ hx)) ha'.2)
      fun t ⟨V, O, R⟩ => ⟨fun x hx => ?_, ?_, (m₁.rest _).trans R⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · have k : t.mem.readW (off base o) 32 = s₁.mem.readW (off base o) 32 :=
          Mem.readW_congr fun i hi => O _ fun w hw => by
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
            have := ha'.1 y hy
            have := (hf y (List.mem_cons_of_mem _ hy)).2
            rw [ofs_off base (by omega)]; omega
        rw [k, m₁.mem]
        exact Mem.readW_writeW_self32 _ _ _
      · rw [V x hx, m₁.gpr]
    · intro x hx
      rw [O x fun w hw => hx w (List.mem_cons_of_mem _ hw), m₁.mem]
      exact writeW32_outside _ _ _ (by omega) x (hx _ (List.mem_cons_self ..))

/-- Loads of distinct registers, none of them `r12`, from offsets of `r12`. -/
theorem loads_ok {base : Addr} {size : Nat} :
    ∀ (l : List (Reg × Nat)) {s : State}, Ws s base size → Fit size l → (∀ x ∈ l, x.1 ≠ .r12) →
      (l.map (·.1)).Nodup →
      WP isa (.block (l.map fun (r, o) => .ldr r .r12 o)) s fun t =>
        (∀ x ∈ l, t.gpr x.1 = s.mem.readW (off base x.2) 32) ∧ Rest (l.map (·.1)) s t ∧ t.mem = s.mem
  | [], s, _, _, _, _ => WP.block_nil ⟨(fun _ h => nomatch h), Rest.refl _ _, rfl⟩
  | (r, o) :: l, s, hs, hf, h12, hd => by
    have nw := hs.nowrap
    obtain ⟨ho, ho'⟩ := hf _ (List.mem_cons_self ..)
    refine wp_ldr ho (hs.ea12 (by omega)) (hs.read ho') fun s₁ v₁ => ?_
    have hd' := List.nodup_cons.mp hd
    refine WP.mono (loads_ok l (hs.of_upd v₁ (h12 _ (List.mem_cons_self ..)))
      (fun x hx => hf x (List.mem_cons_of_mem _ hx)) (fun x hx => h12 x (List.mem_cons_of_mem _ hx)) hd'.2)
      fun t ⟨V, R, M⟩ => ⟨fun x hx => ?_, ?_, M.trans v₁.mem⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [R.gpr _ hd'.1, v₁.gpr]
      · rw [V x hx, v₁.mem]
    · exact (v₁.rest (List.mem_cons_self ..)).trans (R.mono fun _ h => List.mem_cons_of_mem _ h)

theorem slots_eq : slots =
    [(.r4, 8), (.r5, 12), (.r6, 16), (.r7, 20), (.r8, 24), (.r9, 28), (.r10, 32), (.r11, 36), (.lr, 40)] := rfl

theorem slots_fit {size : Nat} (hz : 44 ≤ size) : Fit size slots := by
  intro x hx
  simp only [slots_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by omega⟩

theorem slots_apart : Apart slots := by unfold Apart; decide

theorem slots_r12 : ∀ x ∈ slots, x.1 ≠ .r12 := by decide

theorem slots_nodup : (slots.map (·.1)).Nodup := by decide

/-- Every slot's register is kept by the calling convention. -/
theorem slots_regs : slots.map (·.1) = preserved := rfl

/-- The saved words lie in the header, past `m'` and the mask. -/
theorem slots_words : ∀ r ∈ words slots, 8 ≤ r.1 ∧ r.1 + r.2 ≤ 44 := by decide

/-- Ranges each within one of others. -/
theorem outs_within {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (O : Outs base rs m m')
    (h : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m m' :=
  fun x hx => O x fun r hr => by
    obtain ⟨r', hr', h₁, h₂⟩ := h r hr
    have := hx r' hr'
    omega

/-- A word apart from every range that changed. -/
theorem outs_readW {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (O : Outs base rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_congr fun i hi => O _ fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega)]; omega

/-- The function's working space on entry: `r0` holds its base. -/
structure Entry (s : State) (base : Addr) (size : Nat) : Prop where
  wb : State.addr (s.gpr .r0) = base
  wr : ∃ len, size ≤ len ∧ len ≤ 2 ^ 32 ∧ (⟨base, len⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 32

theorem contextBytes_bounds {n : Nat} (hn : n ≤ 48) : 44 ≤ contextBytes n ∧ contextBytes n ≤ 4960 := by
  simp only [contextBytes, slot, stride]; omega

/-- Ranges in the header's first 64 bytes or past the modulus's slot are the
function's own. -/
theorem within_scratch {n : Nat} {rs : List (Nat × Nat)}
    (h : ∀ r ∈ rs, r.1 + r.2 ≤ 64 ∨ (slot n 1 ≤ r.1 ∧ r.1 + r.2 ≤ contextBytes n)) :
    ∀ r ∈ rs, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := fun r hr =>
  (h r hr).elim (fun h => ⟨(0, 64), List.mem_cons_self .., by simp only; omega⟩)
    fun h => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega⟩

theorem setup_scratch (n : Nat) :
    ∀ r ∈ setupRanges n, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  within_scratch (by
    simp only [setupRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      contextBytes, slot, stride]
    omega)

theorem exponent_scratch {n e : Nat} (he : e ≤ 2 * n) :
    ∀ r ∈ exponentRanges n e, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  within_scratch (by
    simp only [exponentRanges, productRanges, List.cons_append, List.nil_append, List.forall_mem_cons,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, contextBytes, slot, stride, maskO]
    omega)

theorem words_scratch (n : Nat) :
    ∀ r ∈ words slots, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  fun r hr => ⟨(0, 64), List.mem_cons_self .., by have := slots_words r hr; omega⟩

/-- `b ^ x mod m` into slot 9, for the modulus in slot 0, the base in slot 8
and the exponent of `e` words in slot 11; the registers the calling
convention keeps are restored. -/
theorem body_ok {s : State} {base : Addr} {size n e m : Nat} (E : Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (body n e) s fun t =>
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) e % m ∧
      Outs base (scratch n) s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨c44, c4960⟩ := contextBytes_bounds hn48
  have nw := E.nowrap
  have s0 := slot_bound (n := n) (i := 0) (by decide)
  have s8 := slot_bound (n := n) (i := 8) (by decide)
  have s11 := slot_bound (n := n) (i := 11) (by decide)
  have h0 := slot_header n 0
  have h8 := slot_header n 8
  have h11 := slot_header n 11
  unfold body save
  refine WP.seq (wp_mov (op2_reg s .r0) fun s₁ u₁ => ?_)
  have w₁ : Ws s₁ base size := ⟨by rw [u₁.gpr]; exact E.wb, u₁.wr ▸ E.wr, nw⟩
  refine WP.mono (stores_ok slots w₁ (slots_fit (by omega)) slots_apart) fun s₂ ⟨S₂, O₂, R₂⟩ => ?_
  have w₂ := w₁.of_rest R₂ (by decide)
  have away : ∀ {d k : Nat}, 44 ≤ d → d + 4 * k ≤ 2 ^ 64 →
      val32 s₂.mem base d k = val32 s.mem base d k := fun hd hd' => by
    rw [O₂.val32 (fun r hr => .inr (by have := slots_words r hr; omega)) hd', u₁.mem]
  have hv₂ : val32 s₂.mem base (slot n 0) (2 * n) = m := by
    rw [away (by omega) (by simp only [contextBytes, slot, stride] at *; omega)]; exact hv
  refine WP.seq (WP.mono (contextSetup_ok w₂ hn (by omega) (by omega) (by omega) hv₂ hm1 hodd)
    fun s₃ ⟨c₃, one₃, rr₃, O₃, R₃⟩ => ?_)
  refine WP.seq (WP.mono (exponentiate_ok c₃ he hen (by omega) one₃ rr₃) fun s₄ ⟨c₄, V₄, O₄, R₄⟩ => ?_)
  refine WP.mono (loads_ok slots c₄.ws (slots_fit (by omega)) slots_r12 slots_nodup) fun t ⟨L, R₅, M₅⟩ =>
    ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have k₃ : ∀ {d k : Nat}, (∀ r ∈ setupRanges n, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) → d + 4 * k ≤ 2 ^ 64 →
        val32 s₃.mem base d k = val32 s₂.mem base d k := fun h h' => O₃.val32 h h'
    rw [show val32 t.mem base (slot n 9) (2 * n) = val32 s₄.mem base (slot n 9) (2 * n) by rw [M₅], V₄,
      k₃ (by simp only [setupRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]; omega) (by omega),
      k₃ (by simp only [setupRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]; omega) (by omega),
      away (by omega) (by omega), away (by omega) (by omega)]
  · have O₂' : Outs base (scratch n) s.mem s₂.mem := by rw [← u₁.mem]; exact outs_within O₂ (words_scratch n)
    rw [M₅]
    exact (O₂'.trans (outs_within O₃ (setup_scratch n))).trans (outs_within O₄ (exponent_scratch hen))
  · rw [← slots_regs] at hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hx12 := slots_r12 x hx
    have hw := slots_words _ (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
    simp only at hw
    rw [L x hx,
      outs_readW O₄ (by
        simp only [exponentRanges, productRanges, List.cons_append, List.nil_append, List.forall_mem_cons,
          List.not_mem_nil, false_imp_iff, implies_true, and_true, slot, stride, maskO]
        omega) (by omega),
      outs_readW O₃ (by
        simp only [setupRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
          slot, stride]
        omega) (by omega),
      S₂ x hx, u₁.other _ hx12]
  · rw [R₅.sp, R₄.sp, R₃.sp, R₂.sp, u₁.sp]
  · rw [R₅.rd, R₄.rd, R₃.rd, R₂.rd, u₁.rd]
  · rw [R₅.wr, R₄.wr, R₃.wr, R₂.wr, u₁.wr]

/-! ## The function -/

/-- The function's contract in this file's terms: the working space at `r0`,
of `r1` words, and the numbers as `val32` reads them. -/
def powK (n e : Nat) : Contract isa where
  pre s :=
    let base := State.addr (s.gpr .r0)
    let M := val32 s.mem base (slot n 0) (2 * n)
    s.rd = [] ∧ s.wr = [⟨base, (s.gpr .r1).toNat * 8⟩] ∧ (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧
      contextBytes n ≤ (s.gpr .r1).toNat * 8 ∧ M % 2 = 1 ∧ 1 < M
  post s t :=
    let base := State.addr (s.gpr .r0)
    val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) e % val32 s.mem base (slot n 0) (2 * n) ∧
      Outs base (scratch n) s.mem t.mem
  pub s t := s.gpr .r0 = t.gpr .r0

theorem powK_correct {n e : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n) (s : State)
    (h : (powK n e).pre s) :
    ∃ tr t, Exec isa (body n e) s tr t ∧ abiPreserved s t ∧ (powK n e).post s t := by
  obtain ⟨-, hwr, hnw, hz, hodd, hm1⟩ := h
  have E : Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
    ⟨rfl, ⟨_, Nat.le_refl _, by omega, by rw [hwr]; exact List.mem_singleton_self _⟩,
      by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hnw⟩
  obtain ⟨tr, t, ex, V, O, P, hsp, -, -⟩ := body_ok E hz hn hn48 he hen rfl hm1 hodd
  exact ⟨tr, t, ex, ⟨P, hsp⟩, V, O⟩

/-- The registers whose values steer an address or a branch: the working
space's, once `save` copies `r0` to `r12`. -/
theorem body_relCT (n e : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs [.r0])) (body n e) fun _ _ => True := by
  unfold body
  refine RelCT.seq (relCT_of_check (σ := wsT false false) (h := .block []) (by decide)) ?_
  refine RelCT.seq (contextSetup_relCT false false n) (RelCT.seq (exponentiate_relCT false false n e) ?_)
  exact (relCT_of_check (σ := VG.Arm.Taint.ofRegs []) (h := .block []) (by decide)).mono (fun _ _ h => h)
    fun _ _ _ => trivial

theorem powK_ct (n e : Nat) : ConstantTime isa (powK n e).pre (powK n e).pub (body n e) :=
  RelCT.constantTime ((body_relCT n e).mono (fun _ _ h => VG.Arm.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.2.2) fun _ _ h => h)

end VG.Proof.Dsa.Arm.Pow
