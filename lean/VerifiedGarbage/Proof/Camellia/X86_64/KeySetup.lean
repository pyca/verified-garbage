import VerifiedGarbage.Proof.Camellia.X86_64.KaKb
import VerifiedGarbage.Proof.Camellia.X86_64.KeyContract

/-!
# The Camellia key schedule on x86-64: the whole function

`expandKey_wp`: with the working space as an argument (`expandKeyX86_64`),
`expandKey` saves the callee-saved registers, sets the masks, stores the
planes of `Sigma1 … Sigma6` as a table of subkeys (`sigmas_ok`), loads `KL`
and `KR` (`loadKey_wp`), computes `KA` and `KB` (`kaKb_wp`), and stores the
subkeys, halves of their rotations (`storeSubkeys_ok`), before restoring the
registers.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_ slotAt setMasks)
open VG.Proof.Camellia (HalfRel pair hiW loW)

/-! ## Single instructions -/

/-- `mov [sb + 8 k], r`, as slots. -/
theorem st_ok {s : State} {k : Nat} (r : Reg) (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hk : k < slots) :
    ∃ s', runBlock isa [st k r] s = some s' ∧ slotW s' k = s.gpr r ∧
      (∀ j < slots, j ≠ k → slotW s' j = slotW s j) ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e, m, g, rd, wr⟩ := stReg_ok (k := k) r rfl (scr_in hscr hk)
  refine ⟨s', e, ?_, fun j hj hjk => ?_, g, by rw [m]; exact frame_slot _ hk, rd, wr⟩
  · rw [slotW_store m g hk hk, ite_eq_left rfl]
  · rw [slotW_store m g hj hk, ite_eq_right hjk]

/-- `mov d, [r + k]`. -/
theorem ldAt_ok (s : State) (d r : Reg) (k : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 k) 8) :
    ∃ s', runBlock isa [.mov d (.mem (at_ r k))] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr r + BitVec.ofNat 64 k) 64 ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.setReg d (s.mem.readW (s.gpr r + BitVec.ofNat 64 k) 64), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r' h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h], rfl, rfl, rfl⟩
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.ea, ofInt_nat,
    hr, ite_true, Option.map_some]

/-- `mov32 rax, 0`. -/
theorem zeroRax_ok (s : State) :
    ∃ s', runBlock isa [.mov32 .rax (.imm 0)] s = some s' ∧ s'.gpr .rax = 0 ∧
      (∀ r', r' ≠ .rax → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.setReg .rax ((0 : BitVec 32).setWidth 64), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some, State.setReg32],
    by simp only [RegUpd.gpr_setReg_self]; rfl, fun r' h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h],
    rfl, rfl, rfl⟩

/-- `xor rax, 0xFFFFFFFF`: all its bits flipped. -/
theorem notRax_ok (s : State) :
    ∃ s', runBlock isa [.alu .xor .rax (.imm 0xFFFFFFFF)] s = some s' ∧ s'.gpr .rax = ~~~ s.gpr .rax ∧
      (∀ r', r' ≠ .rax → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_, fun r' hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
    rw [show (0xFFFFFFFF : BitVec 32).signExtend 64 = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem WordOf.zero : WordOf 0 0 := fun i hi j hj => by
  rw [Camellia.getLsbD_byteOf _ hi hj]; simp

theorem WordOf.not {w h : BitVec 64} (hw : WordOf w h) : WordOf (~~~ w) (~~~ h) := fun i hi j hj => by
  rw [Camellia.getLsbD_byteOf _ hi hj, BitVec.getLsbD_not, BitVec.getLsbD_not, hw i hi j hj,
    Camellia.getLsbD_byteOf _ hi hj]
  simp only [show 8 * i + j < 64 by omega, show 56 - 8 * i + j < 64 by omega, decide_true, Bool.true_and]

/-! ## The table of `Sigma1 … Sigma6` -/

/-- The first `n` stores of `sigmaOne x`. -/
def sigPairs (x : BitVec 64) (n : Nat) : List Instr :=
  (List.range n).flatMap fun j => [.movImm64 .rax (keyPlane x j), .store (slotAt .rsi j) .rax]

theorem sigPairs_ok (x : BitVec 64) : ∀ n ≤ 8, ∀ s : State,
    (∀ j < 8, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (8 * j)) 8) →
    ∃ s', runBlock isa (sigPairs x n) s = some s' ∧
      (∀ j < n, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * j)) 64 = keyPlane x j) ∧
      Frame [⟨s.gpr .rsi, 64⟩] s.mem s'.mem ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _, s, _ => ⟨s, rfl, fun j hj => absurd hj (by omega), Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  | n + 1, hn, s, hw => by
    obtain ⟨s₁, e₁, v₁, f₁, g₁, rd₁, wr₁⟩ := sigPairs_ok x n (by omega) s hw
    obtain ⟨s₂, e₂, c₂, o₂, m₂, rd₂, wr₂⟩ := movImm_ok s₁ .rax (keyPlane x n)
    have hsi : s₂.gpr .rsi = s.gpr .rsi := by rw [o₂ _ (by decide), g₁ _ (by decide)]
    obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := storeAt_ok s₂ .rsi (8 * n) .rax
      (by rw [wr₂, wr₁, hsi]; exact hw n (by omega))
    have e₃' : runBlock isa [.store (slotAt .rsi n) .rax] s₂ = some s₃ := e₃
    refine ⟨s₃, ?_, fun j hj => ?_, ?_, fun r hr => by rw [g₃, o₂ r hr, g₁ r hr], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩
    · rw [sigPairs, List.range_succ, List.flatMap_append, runBlock_append', ← sigPairs, e₁, Option.bind_some,
        List.flatMap_cons, List.flatMap_nil, List.append_nil,
        show ([.movImm64 .rax (keyPlane x n), .store (slotAt .rsi n) .rax] : List Instr) =
          [.movImm64 .rax (keyPlane x n)] ++ [.store (slotAt .rsi n) .rax] from rfl,
        runBlock_append', e₂, Option.bind_some, e₃']
    · rw [m₃, hsi]
      by_cases hjn : j = n
      · subst hjn; rw [Mem.readW_writeW_self64, c₂]
      · rw [Mem.readW_writeW_sep (VG.Offset.sep _ (by omega) (by omega) (by omega)) (by decide), m₂,
          v₁ j (by omega)]
    · refine f₁.trans ?_
      rw [m₃, m₂, hsi]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (VG.Offset.contains_base _ (by omega) (by omega))

/-- `sigmaOne x`: the planes of `x` to the entry at `rsi`, and `rsi` to the next. -/
theorem sigmaOne_ok (x : BitVec 64) (s : State)
    (hw : ∀ j < 8, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (sigmaOne x) s = some s' ∧
      (∀ j < 8, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * j)) 64 = keyPlane x j) ∧
      s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 64 ∧ Frame [⟨s.gpr .rsi, 64⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, f₁, g₁, rd₁, wr₁⟩ := sigPairs_ok x 8 (Nat.le_refl 8) s hw
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rsi 64
  refine ⟨s₂, by rw [show sigmaOne x = sigPairs x 8 ++ [.alu .add .rsi (.imm 64)] from rfl, runBlock_append',
      e₁, Option.bind_some, e₂], fun j hj => by rw [m₂]; exact v₁ j hj,
    by rw [a₂, g₁ _ (by decide)]; rfl, by rw [m₂]; exact f₁, fun r h1 h2 => by rw [o₂ r h2, g₁ r h1],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- Entry `i` of the table at `b`, as an address from `rsi`. -/
theorem entryW_eq (m : Mem) (b : Addr) (i j : Nat) :
    entryW m b i j = m.readW (b + BitVec.ofNat 64 (8 * keySlot + 64 * i) + BitVec.ofNat 64 (8 * j)) 64 := by
  rw [entryW, addr_add]

theorem sigmaList_ok {b : Addr} (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) :
    ∀ (xs : List (BitVec 64)) (e : Nat) (s : State), (⟨b, 8 * slots⟩ : Region) ∈ s.wr →
      s.gpr .rsi = b + BitVec.ofNat 64 (8 * keySlot + 64 * e) → e + xs.length ≤ 34 →
      ∃ s', runBlock isa (xs.flatMap sigmaOne) s = some s' ∧
        (∀ i < xs.length, ∀ j < 8, entryW s'.mem b (e + i) j = keyPlane (xs.getD i 0) j) ∧
        Frame [⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64 * xs.length⟩] s.mem s'.mem ∧
        s'.gpr .rsi = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e + xs.length)) ∧
        (∀ r, r ≠ .rax → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], e, s, _, hr, _ => ⟨s, rfl, fun i hi => absurd hi (by simp), Frame.refl _ _, by simpa using hr,
      fun _ _ _ => rfl, rfl, rfl⟩
  | x :: xs, e, s, hscr, hr, hl => by
    rw [slots_eq] at hfit
    have hk := keySlot_eq
    simp only [List.length_cons] at hl
    obtain ⟨s₁, e₁, v₁, r₁, f₁, g₁, rd₁, wr₁⟩ := sigmaOne_ok x s (fun j hj => ⟨_, hscr, by
      rw [hr, addr_add]; exact VG.Offset.contains_base _ (by rw [slots_eq]; omega) (by omega)⟩)
    obtain ⟨s', e', v', f', r', g', rd', wr'⟩ := sigmaList_ok hfit xs (e + 1) s₁ (by rw [wr₁]; exact hscr)
      (by rw [r₁, hr, addr_add, show 8 * keySlot + 64 * e + 64 = 8 * keySlot + 64 * (e + 1) by omega])
      (by omega)
    refine ⟨s', by rw [List.flatMap_cons, runBlock_append', e₁, Option.bind_some, e'], fun i hi j hj => ?_,
      ?_, by rw [r', List.length_cons, show e + 1 + xs.length = e + (xs.length + 1) by omega],
      fun r h1 h2 => by rw [g' r h1 h2, g₁ r h1 h2], by rw [rd', rd₁], by rw [wr', wr₁]⟩
    · rcases i with _ | i
      · rw [entryW_eq, Nat.add_zero, ← hr]
        refine (f'.readW (Region.contains_self _ _) (fun r hr' => ?_) (by decide)).trans (v₁ j hj)
        simp only [List.mem_singleton] at hr'; subst hr'
        rw [hr, addr_add]
        exact VG.Offset.disjoint b (by omega) (by omega) (by omega)
      · rw [show e + (i + 1) = e + 1 + i by omega]
        exact v' i (by simpa using hi) j hj
    · refine Frame.trans (f₁.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩)
        (f'.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
        (simp only [List.mem_singleton] at hr'; subst hr')
      · rw [hr]; exact Region.sub_prefix (by simp only [List.length_cons]; omega)
      · exact VG.Offset.sub b (by omega) (by simp only [List.length_cons]; omega)

/-- The table's entries `0 … 5` hold `Sigma1 … Sigma6`, as `KeyCtx` reads them. -/
theorem sigmas_rel {m : Mem} {b : Addr}
    (h : ∀ i < 6, ∀ j < 8, entryW m b i j = keyPlane (sigmas.getD i 0) j) :
    ∀ i < 6, HalfRel (entryW m b i) fun _ => sigE i := fun i hi bb hb c hc j hj => by
  rw [h i hi j hj]; exact sigma_planes _ hb hc hj

/-! ## Loading the key -/

/-- A step that writes only `rax` and the flags. -/
structure Pure (s s' : State) : Prop where
  mem : s'.mem = s.mem
  regs : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Pure.refl (s : State) : Pure s s := ⟨rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Pure.trans {s₁ s₂ s₃ : State} (h₁ : Pure s₁ s₂) (h₂ : Pure s₂ s₃) : Pure s₁ s₃ :=
  ⟨h₂.mem.trans h₁.mem, fun r hr => (h₂.regs r hr).trans (h₁.regs r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

/-- A store of `rax` to slot `k`. -/
structure StOk (s s' : State) (k : Nat) : Prop where
  val : slotW s' k = s.gpr .rax
  keep : ∀ j < slots, j ≠ k → slotW s' j = slotW s j
  gpr : s'.gpr = s.gpr
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem stOk {s : State} {k : Nat} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < slots) :
    ∃ s', runBlock isa [st k .rax] s = some s' ∧ StOk s s' k := by
  obtain ⟨s', e, v, kp, g, f, rd, wr⟩ := st_ok (k := k) .rax hscr hk
  exact ⟨s', e, v, kp, g, f, rd, wr⟩

/-- `KR`'s words stored: what each branch of `loadKey` leaves. -/
structure KrPost (s s' : State) (V : BitVec 64 × BitVec 64) : Prop where
  kr : WordsAt s' krSlot V
  keep : ∀ k < slots, k ≠ krSlot → k ≠ krSlot + 1 → slotW s' k = slotW s k
  regs : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem StOk.frame' {s₀ s s' : State} {k : Nat} (hf : Frame [⟨s₀.gpr sb, 8 * slots⟩] s₀.mem s.mem)
    (hb : s.gpr sb = s₀.gpr sb) (h : StOk s s' k) : Frame [⟨s₀.gpr sb, 8 * slots⟩] s₀.mem s'.mem :=
  hf.trans (by have := h.frame; rw [hb] at this; exact this)

theorem krPost_of {s s₁ s₂ s₃ s₄ : State} {V : BitVec 64 × BitVec 64}
    (p₁ : Pure s s₁) (h₂ : StOk s₁ s₂ krSlot) (p₃ : Pure s₂ s₃) (h₄ : StOk s₃ s₄ (krSlot + 1))
    (hu : WordOf (s₁.gpr .rax) V.1) (hv : WordOf (s₃.gpr .rax) V.2) : KrPost s s₄ V := by
  obtain ⟨-, hr, -, -, -, -, -, hS⟩ := kaKb_slots
  have hb₁ : s₁.gpr sb = s.gpr sb := p₁.regs _ (by decide)
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [p₃.regs _ (by decide), h₂.gpr, hb₁]
  have hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of p₁.mem hb₁
  have hs₃ : ∀ k, slotW s₃ k = slotW s₂ k := slotW_eq_of p₃.mem (by rw [p₃.regs _ (by decide)])
  have f₂ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₂.mem :=
    StOk.frame' (by rw [p₁.mem]; exact Frame.refl _ _) hb₁ h₂
  refine ⟨⟨?_, ?_⟩, fun k hk h1 h2 => by rw [h₄.keep k hk h2, hs₃, h₂.keep k hk h1, hs₁],
    fun r hr => by rw [h₄.gpr, p₃.regs r hr, h₂.gpr, p₁.regs r hr],
    StOk.frame' (by rw [p₃.mem]; exact f₂) hb₃ h₄,
    by rw [h₄.rd, p₃.rd, h₂.rd, p₁.rd], by rw [h₄.wr, p₃.wr, h₂.wr, p₁.wr]⟩
  · rw [h₄.keep _ (by omega) (by omega), hs₃, h₂.val]; exact hu
  · rw [h₄.val]; exact hv

/-- `loadKey`: `KL`'s and `KR`'s halves, as words, in their slots. -/
theorem loadKey_wp {s : State} {len : Nat} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hkey : (⟨s.gpr .rdi, len⟩ : Region) ∈ s.rd) (hfit : (s.gpr .rdi).toNat + len ≤ 2 ^ 64)
    (hks : Region.Disjoint ⟨s.gpr .rdi, len⟩ ⟨s.gpr sb, 8 * slots⟩)
    (hlen : s.gpr .rsi = BitVec.ofNat 64 len) (hl : len = 16 ∨ len = 24 ∨ len = 32) :
    WP isa loadKey s fun s' =>
      WordsAt s' klSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).1,
        loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).1) ∧
      WordsAt s' krSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).2,
        loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).2) ∧
      (∀ k < slots, (k < klSlot ∨ krSlot + 2 ≤ k) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl', hr', -, -, -, -, -, hS⟩ := kaKb_slots
  obtain ⟨hK0, hK1, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .rdi) hl
  -- The key's words, read after stores to the scratch buffer.
  have hkw : ∀ {t : State}, t.rd = s.rd → t.gpr .rdi = s.gpr .rdi →
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem t.mem → ∀ d, d + 8 ≤ len →
      ∃ t', runBlock isa [.mov .rax (.mem (at_ .rdi d))] t = some t' ∧ Pure t t' ∧
        WordOf (t'.gpr .rax) (Spec.Camellia.wordAt s.mem (s.gpr .rdi + BitVec.ofNat 64 d)) := by
    intro t hrd hdi hf d hd
    obtain ⟨t', e, a, o, m, rd, wr⟩ := ldAt_ok t .rax .rdi d (by
      rw [hrd, hdi]; exact ⟨_, List.mem_append_left _ hkey, VG.Offset.contains_base _ (by omega) (by omega)⟩)
    refine ⟨t', e, ⟨m, o, rd, wr⟩, ?_⟩
    rw [a, hdi, hf.readW (r := ⟨s.gpr .rdi + BitVec.ofNat 64 d, 64 / 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hks.sub_left (VG.Offset.sub_base _ (by omega))) (by decide)]
    exact wordOf_readW _ _
  have hz : s.gpr .rdi + BitVec.ofNat 64 0 = s.gpr .rdi := by simp
  have hscrOf : ∀ {t : State}, t.gpr sb = s.gpr sb → t.wr = s.wr → (⟨t.gpr sb, 8 * slots⟩ : Region) ∈ t.wr :=
    fun hb hw => by rw [hb, hw]; exact hscr
  unfold loadKey
  -- `KL`.
  obtain ⟨s₁, e₁, p₁, w₁⟩ := hkw rfl rfl (Frame.refl _ _) 0 (by omega)
  have hb₁ : s₁.gpr sb = s.gpr sb := p₁.regs _ (by decide)
  obtain ⟨s₂, e₂, h₂⟩ := stOk (k := klSlot) (hscrOf hb₁ p₁.wr) (by omega)
  have hb₂ : s₂.gpr sb = s.gpr sb := by rw [h₂.gpr, hb₁]
  have f₂ := StOk.frame' (by rw [p₁.mem]; exact Frame.refl _ _) hb₁ h₂
  obtain ⟨s₃, e₃, p₃, w₃⟩ := hkw (by rw [h₂.rd, p₁.rd]) (by rw [h₂.gpr, p₁.regs _ (by decide)]) f₂ 8 (by omega)
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [p₃.regs _ (by decide), hb₂]
  obtain ⟨s₄, e₄, h₄⟩ := stOk (k := klSlot + 1) (hscrOf hb₃ (by rw [p₃.wr, h₂.wr, p₁.wr])) (by omega)
  have f₄ := StOk.frame' (by rw [p₃.mem]; exact f₂) hb₃ h₄
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := cmpImmZ_ok s₄ .rsi 16
  have hg₅ : ∀ r, r ≠ .rax → s₅.gpr r = s.gpr r := fun r hr => by
    rw [g₅, h₄.gpr, p₃.regs r hr, h₂.gpr, p₁.regs r hr]
  have hb₅ : s₅.gpr sb = s.gpr sb := hg₅ _ (by decide)
  have hs₅ : ∀ k, slotW s₅ k = slotW s₄ k := slotW_eq_of m₅ (by rw [g₅])
  have hs₃ : ∀ k, slotW s₃ k = slotW s₂ k := slotW_eq_of p₃.mem (p₃.regs _ (by decide))
  have hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of p₁.mem hb₁
  have f₅ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₅.mem := by rw [m₅]; exact f₄
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, h₄.rd, p₃.rd, h₂.rd, p₁.rd]
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, h₄.wr, p₃.wr, h₂.wr, p₁.wr]
  have hkl : WordsAt s₅ klSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).1,
      loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).1) := by
    refine ⟨?_, ?_⟩
    · rw [hs₅, h₄.keep _ (by omega) (by omega), hs₃, h₂.val, hK0, ← hz]; exact w₁
    · rw [hs₅, h₄.val, hK1]; exact w₃
  have hother : ∀ k < slots, k ≠ klSlot → k ≠ klSlot + 1 → slotW s₅ k = slotW s k := fun k hk h1 h2 => by
    rw [hs₅, h₄.keep k hk h2, hs₃, h₂.keep k hk h1, hs₁]
  have hz₅ : s₅.zf = some (decide (len = 16)) := by
    rw [z₅, h₄.gpr, p₃.regs _ (by decide), h₂.gpr, p₁.regs _ (by decide), hlen,
      show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₅, by
    rw [show ([.mov .rax (.mem (at_ .rdi 0)), st klSlot .rax, .mov .rax (.mem (at_ .rdi 8)),
        st (klSlot + 1) .rax, .alu .cmp .rsi (.imm 16)] : List Instr) =
        [.mov .rax (.mem (at_ .rdi 0))] ++ ([st klSlot .rax] ++ ([.mov .rax (.mem (at_ .rdi 8))] ++
          ([st (klSlot + 1) .rax] ++ [.alu .cmp .rsi (.imm 16)]))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅], ?_⟩)
  refine WP.mono (Q := fun s' => KrPost s₅ s' (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).2,
      loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).2))
    (WP.ite (decide (len = 16)) (by simp [X86_64.eval, hz₅]) (fun h16 => ?_) (fun h16 => ?_)) fun s' h => ?_
  · -- A key of 16 bytes: `KR = 0`.
    have h16 : len = 16 := by simpa using h16
    obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆⟩ := zeroRax_ok s₅
    have p₆ : Pure s₅ s₆ := ⟨m₆, o₆, rd₆, wr₆⟩
    obtain ⟨s₇, e₇, h₇⟩ := stOk (k := krSlot) (hscrOf (by rw [o₆ _ (by decide), hb₅]) (by rw [wr₆, wr₅']))
      (by omega)
    obtain ⟨s₈, e₈, h₈⟩ := stOk (k := krSlot + 1)
      (hscrOf (by rw [h₇.gpr, o₆ _ (by decide), hb₅]) (by rw [h₇.wr, wr₆, wr₅'])) (by omega)
    refine WP.of_runBlock ⟨s₈, by
      rw [show ([.mov32 .rax (.imm 0), st krSlot .rax, st (krSlot + 1) .rax] : List Instr) =
          [.mov32 .rax (.imm 0)] ++ ([st krSlot .rax] ++ [st (krSlot + 1) .rax]) from rfl,
        runBlock_append', e₆, Option.bind_some, runBlock_append', e₇, Option.bind_some, e₈],
      krPost_of p₆ h₇ (Pure.refl _) h₈ (by rw [a₆, hK2, ite_eq_left h16]; exact WordOf.zero)
        (by rw [h₇.gpr, a₆, hK3, ite_eq_left h16]; exact WordOf.zero)⟩
  · have h16 : len ≠ 16 := by simpa using h16
    obtain ⟨s₆, e₆, p₆, w₆⟩ := hkw (by rw [rd₅']) (hg₅ _ (by decide)) f₅ 16 (by omega)
    have hb₆ : s₆.gpr sb = s.gpr sb := by rw [p₆.regs _ (by decide), hb₅]
    obtain ⟨s₇, e₇, h₇⟩ := stOk (k := krSlot) (hscrOf hb₆ (by rw [p₆.wr, wr₅'])) (by omega)
    obtain ⟨s₈, e₈, z₈, g₈, m₈, rd₈, wr₈⟩ := cmpImmZ_ok s₇ .rsi 24
    have p₈ : Pure s₇ s₈ := ⟨m₈, fun r _ => by rw [g₈], rd₈, wr₈⟩
    have hb₈ : s₈.gpr sb = s.gpr sb := by rw [g₈, h₇.gpr, hb₆]
    have f₈ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₈.mem := by
      rw [m₈]; exact StOk.frame' (by rw [p₆.mem]; exact f₅) hb₆ h₇
    have hz₈ : s₈.zf = some (decide (len = 24)) := by
      rw [z₈, h₇.gpr, p₆.regs _ (by decide), hg₅ _ (by decide), hlen,
        show (24 : BitVec 32).signExtend 64 = BitVec.ofNat 64 24 from rfl,
        VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    refine WP.seq (WP.of_runBlock ⟨s₈, by
      rw [show ([.mov .rax (.mem (at_ .rdi 16)), st krSlot .rax, .alu .cmp .rsi (.imm 24)] : List Instr) =
          [.mov .rax (.mem (at_ .rdi 16))] ++ ([st krSlot .rax] ++ [.alu .cmp .rsi (.imm 24)]) from rfl,
        runBlock_append', e₆, Option.bind_some, runBlock_append', e₇, Option.bind_some, e₈], ?_⟩)
    refine WP.ite (decide (len = 24)) (by simp [X86_64.eval, hz₈]) (fun h24 => ?_) (fun h24 => ?_)
    · have h24 : len = 24 := by simpa using h24
      obtain ⟨s₉, e₉, a₉, o₉, m₉, rd₉, wr₉⟩ := notRax_ok s₈
      obtain ⟨s₁₀, e₁₀, h₁₀⟩ := stOk (k := krSlot + 1)
        (hscrOf (by rw [o₉ _ (by decide), hb₈]) (by rw [wr₉, wr₈, h₇.wr, p₆.wr, wr₅'])) (by omega)
      refine WP.of_runBlock ⟨s₁₀, by
        rw [show ([.alu .xor .rax (.imm 0xFFFFFFFF), st (krSlot + 1) .rax] : List Instr) =
            [.alu .xor .rax (.imm 0xFFFFFFFF)] ++ [st (krSlot + 1) .rax] from rfl,
          runBlock_append', e₉, Option.bind_some, e₁₀],
        krPost_of p₆ h₇ (p₈.trans ⟨m₉, o₉, rd₉, wr₉⟩) h₁₀ (by rw [hK2, ite_eq_right h16]; exact w₆)
          (by rw [a₉, g₈, h₇.gpr, hK3, ite_eq_right h16, ite_eq_left h24]; exact w₆.not)⟩
    · have h24 : len ≠ 24 := by simpa using h24
      obtain ⟨s₉, e₉, p₉, w₉⟩ := hkw (by rw [rd₈, h₇.rd, p₆.rd, rd₅'])
        (by rw [g₈, h₇.gpr, p₆.regs _ (by decide), hg₅ _ (by decide)]) f₈ 24 (by omega)
      obtain ⟨s₁₀, e₁₀, h₁₀⟩ := stOk (k := krSlot + 1)
        (hscrOf (by rw [p₉.regs _ (by decide), hb₈]) (by rw [p₉.wr, wr₈, h₇.wr, p₆.wr, wr₅'])) (by omega)
      refine WP.of_runBlock ⟨s₁₀, by
        rw [show ([.mov .rax (.mem (at_ .rdi 24)), st (krSlot + 1) .rax] : List Instr) =
            [.mov .rax (.mem (at_ .rdi 24))] ++ [st (krSlot + 1) .rax] from rfl,
          runBlock_append', e₉, Option.bind_some, e₁₀],
        krPost_of p₆ h₇ (p₈.trans p₉) h₁₀ (by rw [hK2, ite_eq_right h16]; exact w₆)
          (by rw [hK3, ite_eq_right h16, ite_eq_right h24]; exact w₉)⟩
  · -- Both.
    refine ⟨hkl.congr (h.keep _ (by omega) (by omega) (by omega)) (h.keep _ (by omega) (by omega) (by omega)),
      h.kr, fun k hk h1 => by rw [h.keep k hk (by omega) (by omega), hother k hk (by omega) (by omega)],
      fun r hr => by rw [h.regs r hr, hg₅ r hr], f₅.trans (by have := h.frame; rw [hb₅] at this; exact this),
      by rw [h.rd, rd₅'], by rw [h.wr, wr₅']⟩

/-! ## The schedule's bytes -/

theorem bytesAt_add (m : Mem) (p : Addr) (a n : Nat) :
    Spec.Camellia.bytesAt m p (a + n) =
      Spec.Camellia.bytesAt m p a ++ Spec.Camellia.bytesAt m (p + BitVec.ofNat 64 a) n := by
  simp only [Spec.Camellia.bytesAt, List.range_add, List.map_append, List.map_map]
  refine congrArg (_ ++ ·) (List.map_congr_left fun i _ => ?_)
  show m (p + BitVec.ofNat 64 (a + i)) = m (p + BitVec.ofNat 64 a + BitVec.ofNat 64 i)
  rw [addr_add]

/-- Words stored with their most significant byte first are their `wordBytes`. -/
theorem bytesAt_words (m : Mem) : ∀ (ws : List (BitVec 64)) (p : Addr),
    (∀ i < ws.length, ∀ j < 8, m (p + BitVec.ofNat 64 (8 * i + j)) = Camellia.byteOf (ws.getD i 0) j) →
    Spec.Camellia.bytesAt m p (8 * ws.length) = ws.flatMap Spec.Camellia.wordBytes
  | [], _, _ => rfl
  | w :: ws, p, h => by
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm, bytesAt_add, List.flatMap_cons]
    have h1 : Spec.Camellia.bytesAt m p 8 = Spec.Camellia.wordBytes w := by
      simp only [Spec.Camellia.bytesAt, Spec.Camellia.wordBytes]
      refine List.map_congr_left fun j hj => ?_
      have := h 0 (by simp) j (List.mem_range.mp hj)
      simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at this
      exact this
    rw [h1, bytesAt_words m ws _ fun i hi j hj => ?_]
    rw [addr_add, show 8 + (8 * i + j) = 8 * (i + 1) + j by omega]
    have := h (i + 1) (by simp only [List.length_cons]; omega) j hj
    simp only [List.getD_cons_succ] at this
    exact this

/-! ## Loading the values -/

def lvChunk (v k : Nat) : List Instr :=
  [movS (hiReg v) k, .bswap (hiReg v), movS (loReg v) (k + 1), .bswap (loReg v)]

theorem loadValues_eq :
    loadValues = lvChunk 0 klSlot ++ (lvChunk 1 krSlot ++ (lvChunk 2 kaSlot ++ lvChunk 3 kbSlot)) := rfl

theorem regs_lt4 {v : Nat} (hv : v < 4) : hiReg v ≠ sb ∧ loReg v ≠ sb ∧ hiReg v ≠ loReg v := by
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

theorem lvChunk_ok {s : State} {v k : Nat} (hv : v < 4) (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hk : k + 1 < slots) :
    ∃ s', runBlock isa (lvChunk v k) s = some s' ∧ s'.gpr (hiReg v) = bswap64 (slotW s k) ∧
      s'.gpr (loReg v) = bswap64 (slotW s (k + 1)) ∧
      (∀ r, r ≠ hiReg v → r ≠ loReg v → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨n1, n2, n3⟩ := regs_lt4 hv
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := movS_ok (k := k) (hiReg v) rfl (inRd (scr_in hscr (by omega)))
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := bswap_ok s₁ (hiReg v)
  have hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ n1.symm, o₁ _ n1.symm]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := movS_ok (k := k + 1) (loReg v) hb₂
    (inRd (scr_in (by rw [wr₂, wr₁]; exact hscr) hk))
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := bswap_ok s₃ (loReg v)
  refine ⟨s₄, ?_, ?_, ?_, fun r h1 h2 => by rw [o₄ r h2, o₃ r h2, o₂ r h1, o₁ r h1],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [lvChunk, show ([movS (hiReg v) k, .bswap (hiReg v), movS (loReg v) (k + 1), .bswap (loReg v)] :
        List Instr) = [movS (hiReg v) k] ++ ([.bswap (hiReg v)] ++ ([movS (loReg v) (k + 1)] ++
          [.bswap (loReg v)])) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, e₄]
  · rw [o₄ _ n3, o₃ _ n3, a₂, a₁]
  · rw [a₄, a₃, slotW_eq_of (by rw [m₂, m₁]) hb₂]

/-- `loadValues`: the four values' halves, byte-swapped into `hiReg v` and `loReg v`. -/
theorem loadValues_ok {s : State} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (vs : List (BitVec 128))
    (hw : ∀ v < 4, WordsAt s ([klSlot, krSlot, kaSlot, kbSlot].getD v 0) (hiW (vs.getD v 0), loW (vs.getD v 0))) :
    ∃ s', runBlock isa loadValues s = some s' ∧
      (∀ v < 4, s'.gpr (hiReg v) = hiW (vs.getD v 0) ∧ s'.gpr (loReg v) = loW (vs.getD v 0)) ∧
      (∀ r, (∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl, hr, hW, hA, hB, -, -, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, h₁, l₁, o₁, m₁, rd₁, wr₁⟩ := lvChunk_ok (v := 0) (k := klSlot) (by decide) hscr (by omega)
  have hb₁ : s₁.gpr sb = s.gpr sb := o₁ _ (by decide) (by decide)
  have hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ hb₁
  obtain ⟨s₂, e₂, h₂, l₂, o₂, m₂, rd₂, wr₂⟩ := lvChunk_ok (v := 1) (k := krSlot) (by decide)
    (by rw [hb₁, wr₁]; exact hscr) (by omega)
  have hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide) (by decide), hb₁]
  have hs₂ : ∀ k, slotW s₂ k = slotW s k := fun k => by rw [slotW_eq_of m₂ (by rw [hb₂, hb₁]), hs₁]
  obtain ⟨s₃, e₃, h₃, l₃, o₃, m₃, rd₃, wr₃⟩ := lvChunk_ok (v := 2) (k := kaSlot) (by decide)
    (by rw [hb₂, wr₂, wr₁]; exact hscr) (by omega)
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [o₃ _ (by decide) (by decide), hb₂]
  have hs₃ : ∀ k, slotW s₃ k = slotW s k := fun k => by rw [slotW_eq_of m₃ (by rw [hb₃, hb₂]), hs₂]
  obtain ⟨s₄, e₄, h₄, l₄, o₄, m₄, rd₄, wr₄⟩ := lvChunk_ok (v := 3) (k := kbSlot) (by decide)
    (by rw [hb₃, wr₃, wr₂, wr₁]; exact hscr) (by omega)
  refine ⟨s₄, by rw [loadValues_eq, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂,
      Option.bind_some, runBlock_append', e₃, Option.bind_some, e₄], fun v hv => ?_,
    fun r hr => by
      obtain ⟨a0, b0⟩ := hr 0 (by decide); obtain ⟨a1, b1⟩ := hr 1 (by decide)
      obtain ⟨a2, b2⟩ := hr 2 (by decide); obtain ⟨a3, b3⟩ := hr 3 (by decide)
      rw [o₄ r a3 b3, o₃ r a2 b2, o₂ r a1 b1, o₁ r a0 b0],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl
  · have w := hw 0 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), o₂ _ (by decide) (by decide), h₁]
      exact bswap_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), o₂ _ (by decide) (by decide), l₁]
      exact bswap_of_wordOf w.2
  · have w := hw 1 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), h₂, hs₁]
      exact bswap_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), l₂, hs₁]
      exact bswap_of_wordOf w.2
  · have w := hw 2 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), h₃, hs₂]; exact bswap_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), l₃, hs₂]; exact bswap_of_wordOf w.2
  · have w := hw 3 (by decide)
    exact ⟨by rw [h₄, hs₃]; exact bswap_of_wordOf w.1, by rw [l₄, hs₃]; exact bswap_of_wordOf w.2⟩

/-! ## The prologue -/

theorem sreg_ne' (i : Nat) : sreg i ≠ .r9 ∧ sreg i ≠ .rax ∧ sreg i ≠ .rsi := by
  unfold sreg; split <;> decide

/-- A frame of slots below the tail buffer's. -/
theorem frame_tail {m : Mem} {b : Addr} {k : Nat} (v : BitVec 64) (hk : k < tailSlot) :
    Frame [⟨b, 8 * tailSlot⟩] m (m.writeW (wordAddr b k) v) :=
  frame_writeW v (by rw [wordAddr]; rw [tailSlot_eq] at hk; exact VG.Offset.sub_base _ (by rw [tailSlot_eq]; omega))

theorem ekPrologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .rcx = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr)
    (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) :
    ∃ s, runBlock isa ([movR .r9 .rcx] ++ saveRegs ++ setMasks layerMasks ++ [st dataSlot .rsi] ++
        [movR .rsi sb, .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * keySlot)))] ++
        sigmas.flatMap sigmaOne ++ [movS .rsi dataSlot]) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .rsi = s₀.gpr .rsi ∧
      (∀ r, r ≠ .r9 → r ≠ .rax → r ≠ t0 → r ≠ .rsi → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧ slotW s dataSlot = s₀.gpr .rsi ∧
      (∀ i < 6, ∀ j < 8, entryW s.mem b i j = keyPlane (sigmas.getD i 0) j) ∧
      Frame [⟨b, 8 * tailSlot⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hk := keySlot_eq
  have hd : dataSlot = 369 := rfl
  have ht := tailSlot_eq
  have hsv : savedSlot = 371 := rfl
  have hS := slots_eq
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ .r9 .rcx
  have hb₁ : s₁.gpr sb = b := by rw [show sb = .r9 from rfl, r₁, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (b := b) (by rw [wr₁]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, k₃, g₃, rd₃, wr₃, f₃⟩ := setMasks_ok (b := b) layerMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁]; exact hw) (fun kv hkv => mask_lt hkv) (by decide)
  have hb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide), g₂, hb₁]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stReg_ok (k := dataSlot) .rsi hb₃
    (scr_in (by rw [wr₃, wr₂, wr₁]; exact hw) (by omega))
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := movR_ok s₄ .rsi sb
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := addImm_ok s₅ .rsi (BitVec.ofNat 32 (8 * keySlot))
  have hb₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₅ _ (by decide), g₄, hb₃]
  obtain ⟨s₇, e₇, v₇, f₇, r₇, g₇, rd₇, wr₇⟩ := sigmaList_ok hfit sigmas 0 s₆
    (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hw)
    (by rw [r₆, r₅, g₄, hb₃, show (BitVec.ofNat 32 (8 * keySlot)).signExtend 64 = BitVec.ofNat 64 (8 * keySlot)
      from rfl]; rfl) (by decide)
  have hb₇ : s₇.gpr sb = b := by rw [g₇ _ (by decide) (by decide), hb₆]
  -- The slots outside the table keep their values.
  have hs₇ : ∀ k, k < keySlot ∨ keySlot + 48 ≤ k → k < slots → slotW s₇ k = slotW s₄ k := fun k h1 h2 => by
    simp only [slotW, hb₇, g₄, hb₃]
    rw [← m₅, ← m₆]
    refine f₇.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    simp only [wordAddr, Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
    exact VG.Offset.disjoint b (by omega) (by omega) (by omega)
  obtain ⟨s₈, e₈, a₈, o₈, m₈, rd₈, wr₈⟩ := movS_ok (k := dataSlot) .rsi hb₇
    (inRd (scr_in (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hw) (by omega)))
  have hb₈ : s₈.gpr sb = b := by rw [o₈ _ (by decide), hb₇]
  have hs₈ : ∀ k, slotW s₈ k = slotW s₇ k := slotW_eq_of m₈ (by rw [hb₈, hb₇])
  have hs₄ : ∀ k < slots, k ≠ dataSlot → slotW s₄ k = slotW s₃ k := fun k hk' hkd => by
    rw [slotW_store (by rw [m₄, hb₃]) g₄ hk' (by omega), ite_eq_right hkd]
  have hds : slotW s₄ dataSlot = s₀.gpr .rsi := by
    rw [slotW_store (by rw [m₄, hb₃]) g₄ (by omega) (by omega), ite_eq_left rfl, g₃ _ (by decide), g₂,
      o₁ _ (by decide)]
  refine ⟨s₈, ?_, hb₈, ?_, fun r h1 h2 h3 h4 => ?_, fun i hi => ?_, fun kv hkv => ?_, ?_,
    fun i hi j hj => ?_, ?_, by rw [rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [runBlock_append', runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some,
      e₄, Option.bind_some,
      show ([movR .rsi sb, .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * keySlot)))] : List Instr) =
        [movR .rsi sb] ++ [.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * keySlot)))] from rfl,
      runBlock_append', e₅, Option.bind_some, e₆, Option.bind_some, e₇, Option.bind_some, e₈]
  · rw [a₈, hs₇ _ (Or.inr (by omega)) (by omega), hds]
  · rw [o₈ r h4, g₇ r h2 h4, o₆ r h4, o₅ r h4, g₄, g₃ r h3, g₂, o₁ r h1]
  · obtain ⟨n1, n2, n3⟩ := sreg_ne' i
    have := sv₂ i hi
    rw [show s₁.gpr (sreg i) = s₀.gpr (sreg i) from o₁ _ n1] at this
    rw [← this]
    have h' := hs₇ (savedSlot + i) (Or.inr (by omega)) (by omega)
    rw [hs₄ _ (by omega) (by omega)] at h'
    simp only [slotW, hb₇, hb₃, m₈] at h' ⊢
    rw [h']
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by omega) (by omega)
  · have := mask_lt hkv
    rw [hs₈, hs₇ _ (Or.inl this) (by omega), hs₄ _ (by omega) (by omega)]
    exact v₃ kv hkv
  · rw [hs₈, hs₇ _ (Or.inr (by omega)) (by omega), hds]
  · rw [m₈, ← hb₆]
    have := v₇ i (by simpa [sigmas] using hi) j hj
    rw [Nat.zero_add] at this
    rw [hb₆]; exact this
  · rw [m₈]
    have f₄ : Frame [⟨b, 8 * tailSlot⟩] s₃.mem s₄.mem := by rw [m₄]; exact frame_tail _ (by omega)
    have f₇' : Frame [⟨b, 8 * tailSlot⟩] s₆.mem s₇.mem := f₇.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
      exact VG.Offset.sub_base b (by omega)⟩
    have f₃' : Frame [⟨b, 8 * tailSlot⟩] s₂.mem s₃.mem := f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by omega)⟩
    rw [m₁] at f₂
    exact f₂.trans (f₃'.trans (f₄.trans (by rw [← m₅, ← m₆]; exact f₇')))

end VG.Proof.Camellia.X86_64
