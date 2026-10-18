module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # Array geometry and memory frames shared by 32-bit RSA key operations -/

@[expose] public section
namespace VG.Proof.Rsa.KeyWorkspace
open VG VG.Proof.Mont

def hdr : Nat := 160
abbrev S (w : Nat) : Nat := 4 * (w + 2)
abbrev arr (w j : Nat) : Nat := hdr + j * S w
abbrev num (m : Mem) (B : Addr) (w j : Nat) : Nat := val32 m B (arr w j) w
abbrev slot (m : Mem) (B : Addr) (d : Nat) : Nat := w32 m B d

theorem arr_succ (w j : Nat) : arr w (j + 1) = arr w j + S w := by
  simp only [arr, Nat.succ_mul, Nat.add_assoc]

theorem arr_mono {w j k : Nat} (h : j ≤ k) : arr w j ≤ arr w k :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem arr_end {w j k : Nat} (h : j < k) : arr w j + S w ≤ arr w k := by
  rw [← arr_succ]; exact arr_mono h

theorem arr_disj {w j k : Nat} (h : j ≠ k) : arr w j + S w ≤ arr w k ∨ arr w k + S w ≤ arr w j := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact .inl (arr_end h)
  · exact .inr (arr_end h)

/-! ## Frames -/

/-- The bytes of the arrays `js` and the header words `ds`. -/
def ranges (w : Nat) (js ds : List Nat) : List (Nat × Nat) :=
  js.map (fun j => (arr w j, S w)) ++ ds.map (fun d => (d, 4))

/-- `m'` is `m` but on the arrays `js` and the header words `ds`. -/
def Keep (B : Addr) (w : Nat) (js ds : List Nat) (m m' : Mem) : Prop :=
  Outs B (ranges w js ds) m m'

theorem Keep.refl (B : Addr) (w : Nat) (js ds : List Nat) (m : Mem) : Keep B w js ds m m :=
  Outs.refl _ _ _

theorem Keep.trans {B : Addr} {w : Nat} {js ds : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Keep B w js ds m₁ m₂) (h₂ : Keep B w js ds m₂ m₃) : Keep B w js ds m₁ m₃ :=
  Outs.trans h₁ h₂

theorem Keep.mono {B : Addr} {w : Nat} {js ds js' ds' : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') (hj : ∀ j ∈ js, j ∈ js' := by simp)
    (hd : ∀ d ∈ ds, d ∈ ds' := by simp) : Keep B w js' ds' m m' := by
  refine Outs.mono h fun r hr => ?_
  simp only [ranges, List.mem_append, List.mem_map] at hr ⊢
  rcases hr with ⟨j, hj', rfl⟩ | ⟨d, hd', rfl⟩
  · exact .inl ⟨j, hj j hj', rfl⟩
  · exact .inr ⟨d, hd d hd', rfl⟩

/-- Two frames, each widened to the union. -/
theorem Keep.join {B : Addr} {w : Nat} {js₁ ds₁ js₂ ds₂ js ds : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Keep B w js₁ ds₁ m₁ m₂) (h₂ : Keep B w js₂ ds₂ m₂ m₃)
    (hj₁ : ∀ j ∈ js₁, j ∈ js := by simp) (hd₁ : ∀ d ∈ ds₁, d ∈ ds := by simp)
    (hj₂ : ∀ j ∈ js₂, j ∈ js := by simp) (hd₂ : ∀ d ∈ ds₂, d ∈ ds := by simp) :
    Keep B w js ds m₁ m₃ :=
  (h₁.mono hj₁ hd₁).trans (h₂.mono hj₂ hd₂)

theorem Keep.of_arr {B : Addr} {w o n d : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside B (arr w o + d) n m m') (hn : d + n ≤ S w) (ho : o ∈ js) :
    Keep B w js ds m m' := by
  intro x hx
  have := hx (arr w o, S w) (by simp only [ranges, List.mem_append, List.mem_map]; exact .inl ⟨o, ho, rfl⟩)
  exact h x (by omega)

theorem Keep.of_slot {B : Addr} {w e : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside B e 4 m m') (he : e ∈ ds) : Keep B w js ds m m' := by
  intro x hx
  have := hx (e, 4) (by simp only [ranges, List.mem_append, List.mem_map]; exact .inr ⟨e, he, rfl⟩)
  exact h x this

/-- An array outside the frame. -/
theorem Keep.num {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) : num m' B w j = num m B w j := by
  have hS : 4 * w ≤ S w := by simp only [S]; omega
  refine Outs.val32 h (fun r hr => ?_) (by omega)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj k hk); dsimp only; omega
  · have := hd d hd'; have : hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega

/-- All the words of an array outside the frame. -/
theorem Keep.full {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) :
    val32 m' B (arr w j) (w + 2) = val32 m B (arr w j) (w + 2) := by
  refine Outs.val32 h (fun r hr => ?_) (by simp only [S] at fit; omega)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj k hk); dsimp only; simp only [S] at *; omega
  · have := hd d hd'; have : hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega

/-- A word of an array outside the frame. -/
theorem Keep.word {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {j i : Nat} (hi : 4 * i + 4 ≤ S w) (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    w32 m' B (arr w j + 4 * i) = w32 m B (arr w j + 4 * i) := by
  have := Outs.val32 (k := 1) (d := arr w j + 4 * i) h (fun r hr => ?_) (by omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj k hk); dsimp only; omega
  · have := hd d hd'; have : hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega

/-- A header word outside the frame. -/
theorem Keep.slot {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {e : Nat} (he : e + 4 ≤ hdr) (hd : ∀ d ∈ ds, e + 4 ≤ d ∨ d + 4 ≤ e) :
    slot m' B e = slot m B e := by
  have := Outs.val32 (k := 1) (d := e) h (fun r hr => ?_) (by simp only [hdr] at he; omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have : hdr ≤ arr w k := Nat.le_add_right _ _; dsimp only; omega
  · exact hd d hd'

/-- Memory outside the working space. -/
theorem Keep.out {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {Z : Nat} (hj : ∀ j ∈ js, arr w j + S w ≤ Z) (hd : ∀ d ∈ ds, d + 4 ≤ Z)
    {x : Addr} (hx : Z ≤ ofs B x) : m' x = m x := by
  refine h x fun r hr => ?_
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := hj k hk; dsimp only; omega
  · have := hd d hd'; dsimp only; omega


theorem num_write0 (m : Mem) (B : Addr) {w j : Nat} (hw : 0 < w) (fit : arr w j + 4 * w ≤ 2 ^ 64)
    (v : BitVec 32) :
    num (m.writeW (off B (arr w j)) v) B w j = v.toNat + 2 ^ 32 * (num m B w j / 2 ^ 32) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  have o := writeW32_outside m B (d := arr (k + 1) j) v (by omega)
  have tail := o.val32 (d := arr (k + 1) j + 4) (k := k) (by omega) (by omega)
  simp only [num] at tail ⊢
  rw [val32, val32, w32_write_self, tail]
  have : w32 m B (arr (k + 1) j) < 2 ^ 32 := (m.readW _ 32).isLt
  omega

theorem num_mod2 (m : Mem) (B : Addr) {w j : Nat} (hw : 0 < w) :
    num m B w j % 2 = w32 m B (arr w j) % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [num]; rw [val32]; omega

theorem num_mod32 (m : Mem) (B : Addr) {w j : Nat} (hw : 0 < w) :
    num m B w j % 2 ^ 32 = w32 m B (arr w j) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [num]; rw [val32]
  have : w32 m B (arr (k + 1) j) < 2 ^ 32 := (m.readW _ 32).isLt
  omega

theorem val32_zero_part {m : Mem} {base : Addr} {d K : Nat} (h : val32 m base d K = 0) {a c : Nat}
    (hac : a + c ≤ K) : val32 m base (d + 4 * a) c = 0 := by
  have e1 := val32_append m base d a (K - a)
  rw [show a + (K - a) = K by omega, h] at e1
  have p := Nat.two_pow_pos (32 * a)
  have z : val32 m base (d + 4 * a) (K - a) = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m base (d + 4 * a) (K - a)) with e | e
    · exact e
    · have : 0 < 2 ^ (32 * a) * val32 m base (d + 4 * a) (K - a) := Nat.mul_pos p e
      omega
  have e2 := val32_append m base (d + 4 * a) c (K - a - c)
  rw [show c + (K - a - c) = K - a by omega, z] at e2
  omega

end VG.Proof.Rsa.KeyWorkspace
