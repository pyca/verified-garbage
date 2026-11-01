module

public import VerifiedGarbage.Impl.Dsa.Arm.Pow
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Dsa.ModPowContract

/-! # Workspace register saves and byte/word conversions shared by DSA helpers -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.Pow
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow
open VG.Proof.Dsa.ModPow (numAt)
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

theorem setup_scratch {n : Nat} (hn : 0 < n) :
    ∀ r ∈ Impl.Dsa.Arm.Context.scratch n, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  within_scratch (by
    simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS,
      List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      contextBytes, slot, stride]
    omega)

theorem words_scratch (n : Nat) :
    ∀ r ∈ words slots, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  fun r hr => ⟨(0, 64), List.mem_cons_self .., by have := slots_words r hr; omega⟩


/-- The `4k` bytes at `base + d` are its `k` 32-bit words. -/
theorem read_eq_val32 (m : Mem) (base : Addr) : ∀ (k d : Nat),
    (m.read (off base d) (4 * k)).toNat = val32 m base d k
  | 0, d => by simp [Mem.read, val32]
  | k + 1, d => by
    rw [show 4 * (k + 1) = 4 * k + 4 from rfl, read_toNat_add, val32, ← read_eq_val32 m base k (d + 4),
      Offset.add_add]
    congr 1

theorem numAt_eq8 (m : Mem) (base : Addr) (d n : Nat) : numAt m base d (8 * n) = val32 m base d (2 * n) := by
  rw [← wordsVal_eq_val32, ← read_eq_wordsVal]; rfl

theorem numAt_eq4 (m : Mem) (base : Addr) (d e : Nat) : numAt m base d (4 * e) = val32 m base d e := by
  rw [← read_eq_val32]; rfl


/-- Bytes of 1: an odd number, above 255 when there are at least two. -/
theorem read_ones (a : Addr) : ∀ k, (Mem.read (fun _ => 1) a (k + 2)).toNat % 2 = 1 ∧
    255 < (Mem.read (fun _ => 1) a (k + 2)).toNat := by
  intro k
  rw [VG.Proof.Mont.read_toNat_succ, VG.Proof.Mont.read_toNat_succ]
  rw [show (1 : BitVec 8).toNat = 1 from rfl]
  omega


/-- The context's bytes, in words: the function's `ws_len`. -/
theorem words_eq {n : Nat} (hn48 : n ≤ 48) :
    ((BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32).toNat * 8 = contextBytes n := by
  have h : contextBytes n / 8 < 2 ^ 16 := by simp only [contextBytes, slot, stride]; omega
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
  simp only [contextBytes, slot, stride]
  omega


/-- The context's region, within the working space's. -/
theorem covers_ctx {s : State} {base : Addr} {size n : Nat} (hs : Ws s base size) (hz : contextBytes n ≤ size) :
    Covers [⟨base, contextBytes n⟩] s.wr := by
  have h := hs.write (d := 0) (n := contextBytes n) (by omega)
  rw [show off base 0 = base from BitVec.add_zero _] at h
  exact Covers.one h


end VG.Proof.Dsa.Arm.Pow
