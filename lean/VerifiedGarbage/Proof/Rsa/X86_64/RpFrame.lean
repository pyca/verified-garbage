import VerifiedGarbage.Proof.Rsa.X86_64.RpHalf

/-!
# `vg_rsa_recover_primes` on x86-64: what the pieces change

`rg w js hs`: the arrays `js` and the header slots `hs`, as ranges of the
working space. A piece changes only some of them (`Frm B (rg w js hs)`), and
an array or a slot that is not listed keeps its value (`Frm.rg_wv`,
`Frm.rg_word`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The ranges of the arrays `js` and the header slots `hs`. -/
def rg (w : Nat) (js hs : List Nat) : List (Nat × Nat) :=
  js.map (fun j => (slot w j, 8 * (w + 2))) ++ hs.map (fun i => (8 * i, 8))

theorem rg_mem_arr {w j : Nat} {js : List Nat} (hs : List Nat) (hj : j ∈ js) :
    (slot w j, 8 * (w + 2)) ∈ rg w js hs :=
  List.mem_append_left _ (List.mem_map_of_mem hj)

theorem rg_mem_hdr {w i : Nat} (js : List Nat) {hs : List Nat} (hi : i ∈ hs) : (8 * i, 8) ∈ rg w js hs :=
  List.mem_append_right _ (List.mem_map_of_mem (f := fun i => (8 * i, 8)) hi)

theorem rg_rmut {w : Nat} {js hs : List Nat} (h : ∀ i ∈ hs, rSlot i = true) : ∀ r ∈ rg w js hs, RMut r := by
  intro r hr
  simp only [rg, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, _, rfl⟩ | ⟨i, hi, rfl⟩
  · exact RMut.ofSlot _ _ _
  · exact RMut.hdr (h i hi)

theorem slot_mono {w j k : Nat} (h : j ≤ k) : slot w j ≤ slot w k := by
  unfold slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) h
  omega

theorem slot_add (w j k : Nat) : slot w (j + k) = slot w j + k * (8 * (w + 2)) := by
  unfold slot; rw [Nat.add_mul]; omega

/-- A range within the arrays `j` to `j + K - 1`, none of them in `js`, is
outside `rg w js hs`. -/
theorem rg_sep {w : Nat} {js hs : List Nat} (hhs : ∀ i ∈ hs, i < 32) {j K : Nat}
    (hjs : ∀ k ∈ js, k < j ∨ j + K ≤ k) {d n : Nat} (hd : slot w j ≤ d) (hdn : d + 8 * n ≤ slot w (j + K)) :
    ∀ r ∈ rg w js hs, d + 8 * n ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  intro r hr
  simp only [rg, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨i, hi, rfl⟩
  · dsimp only
    rcases hjs k hk with h | h
    · have := slot_lt (w := w) h; omega
    · have := slot_mono (w := w) h; omega
  · have := hdr_lt_slot w j (hhs i hi); dsimp only; omega

/-- An array not in `js` keeps its value. -/
theorem _root_.VG.Proof.Bignum.Frm.rg_wv {B : Addr} {w : Nat} {js hs : List Nat} {m m' : Mem} (h : Frm B (rg w js hs) m m')
    (hZ : slot w 16 ≤ 2 ^ 64) (hhs : ∀ i ∈ hs, i < 32) {j : Nat} (hj : j < 16) (hjs : j ∉ js) {n : Nat}
    (hn : n ≤ w + 2) : wv m' B (slot w j) n = wv m B (slot w j) n := by
  have h1 := slot_lt (w := w) hj
  have h2 := slot_add w j 1
  exact h.wv_eq (rg_sep hhs (K := 1) (fun k hk => by
    have : k ≠ j := fun e => hjs (e ▸ hk); omega) (Nat.le_refl _) (by omega)) (by omega)

/-- Two arrays `j` and `j + 1` not in `js` keep their value. -/
theorem _root_.VG.Proof.Bignum.Frm.rg_wv2 {B : Addr} {w : Nat} {js hs : List Nat} {m m' : Mem} (h : Frm B (rg w js hs) m m')
    (hZ : slot w 16 ≤ 2 ^ 64) (hhs : ∀ i ∈ hs, i < 32) {j : Nat} (hj : j + 1 < 16) (hjs : j ∉ js)
    (hjs' : j + 1 ∉ js) {n : Nat} (hn : n ≤ 2 * (w + 2)) : wv m' B (slot w j) n = wv m B (slot w j) n := by
  have h1 := slot_lt (w := w) hj
  have h2 := slot_add w j 1
  have h3 := slot_add w j 2
  exact h.wv_eq (rg_sep hhs (K := 2) (fun k hk => by
    have : k ≠ j := fun e => hjs (e ▸ hk)
    have : k ≠ j + 1 := fun e => hjs' (e ▸ hk)
    omega) (Nat.le_refl _) (by omega)) (by omega)

/-- A word of an array not in `js` keeps its value. -/
theorem _root_.VG.Proof.Bignum.Frm.rg_wordA {B : Addr} {w : Nat} {js hs : List Nat} {m m' : Mem} (h : Frm B (rg w js hs) m m')
    (hZ : slot w 16 ≤ 2 ^ 64) (hhs : ∀ i ∈ hs, i < 32) {j : Nat} (hj : j < 16) (hjs : j ∉ js) {i : Nat}
    (hi : i < w + 2) : word m' B (slot w j + 8 * i) = word m B (slot w j + 8 * i) := by
  have h1 := slot_lt (w := w) hj
  have h2 := slot_add w j 1
  have := rg_sep (w := w) (js := js) hhs (K := 1) (j := j) (fun k hk => by
    have : k ≠ j := fun e => hjs (e ▸ hk); omega) (d := slot w j + 8 * i) (n := 1) (by omega) (by omega)
  exact h.word_eq this (by omega)

/-- The low word of an array not in `js` keeps its value. -/
theorem _root_.VG.Proof.Bignum.Frm.rg_word0 {B : Addr} {w : Nat} {js hs : List Nat} {m m' : Mem} (h : Frm B (rg w js hs) m m')
    (hZ : slot w 16 ≤ 2 ^ 64) (hhs : ∀ i ∈ hs, i < 32) {j : Nat} (hj : j < 16) (hjs : j ∉ js) :
    word m' B (slot w j) = word m B (slot w j) := by
  have := h.rg_wordA hZ hhs hj hjs (i := 0) (by omega)
  simpa using this

/-- A header slot not in `hs` keeps its value. -/
theorem _root_.VG.Proof.Bignum.Frm.rg_word {B : Addr} {w : Nat} {js hs : List Nat} {m m' : Mem} (h : Frm B (rg w js hs) m m')
    {i : Nat} (hi : i < 32) (his : i ∉ hs) : word m' B (8 * i) = word m B (8 * i) := by
  refine h.word_eq (fun r hr => ?_) (by omega)
  simp only [rg, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, _, rfl⟩ | ⟨k, hk, rfl⟩
  · have := hdr_lt_slot w k hi; dsimp only; omega
  · have : k ≠ i := fun e => his (e ▸ hk); dsimp only; omega

theorem _root_.VG.Proof.Bignum.Frm.rg_mono {B : Addr} {w : Nat} {js hs js' hs' : List Nat} {m m' : Mem} (h : Frm B (rg w js hs) m m')
    (hj : ∀ j ∈ js, j ∈ js') (hh : ∀ i ∈ hs, i ∈ hs') : Frm B (rg w js' hs') m m' :=
  h.mono fun r hr => by
    simp only [rg, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨j, hj', rfl⟩ | ⟨i, hi, rfl⟩
    · exact rg_mem_arr _ (hj j hj')
    · exact rg_mem_hdr _ (hh i hi)

theorem _root_.VG.Proof.Bignum.Frm.rg_trans {B : Addr} {w : Nat} {js hs js' hs' : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Frm B (rg w js hs) m₁ m₂) (h₂ : Frm B (rg w js' hs') m₂ m₃) :
    Frm B (rg w (js ++ js') (hs ++ hs')) m₁ m₃ :=
  Frm.trans (h₁.rg_mono (fun _ hj => List.mem_append_left _ hj) (fun _ hi => List.mem_append_left _ hi))
    (h₂.rg_mono (fun _ hj => List.mem_append_right _ hj) (fun _ hi => List.mem_append_right _ hi))

/-- A change within array `j`. -/
theorem _root_.VG.Proof.Bignum.Frm.rg_of_out {B : Addr} {w : Nat} {m m' : Mem} {j n : Nat} (h : Outside B (slot w j) n m m')
    (hn : n ≤ 8 * (w + 2)) (js hs : List Nat) (hj : j ∈ js) : Frm B (rg w js hs) m m' :=
  fun x hx => h x (by have := hx _ (rg_mem_arr hs hj); dsimp only at this; omega)

/-- A change within arrays `j` and `j + 1`. -/
theorem _root_.VG.Proof.Bignum.Frm.rg_of_out2 {B : Addr} {w : Nat} {m m' : Mem} {j n : Nat} (h : Outside B (slot w j) n m m')
    (hn : n ≤ 16 * (w + 2)) (js hs : List Nat) (hj : j ∈ js) (hj' : j + 1 ∈ js) : Frm B (rg w js hs) m m' :=
  fun x hx => h x (by
    have := hx _ (rg_mem_arr hs hj)
    have := hx _ (rg_mem_arr hs hj')
    have := slot_add w j 1
    dsimp only at *; omega)

/-- A change within header slot `i`. -/
theorem _root_.VG.Proof.Bignum.Frm.rg_of_hdr {B : Addr} {w : Nat} {m m' : Mem} {i : Nat} (h : Outside B (8 * i) 8 m m')
    (js hs : List Nat) (hi : i ∈ hs) : Frm B (rg w js hs) m m' :=
  Frm.of_outside h (rg_mem_hdr js hi)

/-- A change within the arrays `js'` (of `Arrays`), all in `js`. -/
theorem _root_.VG.Proof.Bignum.Frm.rg_of_arrays {B : Addr} {w : Nat} {js' : List Nat} {m m' : Mem} (h : Arrays B w js' m m')
    (js hs : List Nat) (hj : ∀ j ∈ js', j ∈ js) : Frm B (rg w js hs) m m' :=
  Frm.of_arrays h fun j hj' => rg_mem_arr hs (hj j hj')

/-- A frame of ranges each within one of `rs'`. -/
theorem _root_.VG.Proof.Bignum.Frm.widen {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem}
    (h : Frm B rs m m') (hc : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' :=
  fun x hx => h x fun r hr => by
    obtain ⟨r', hr', a, b⟩ := hc r hr
    have := hx r' hr'
    omega

theorem rg_cover_arr {w j n d : Nat} {js : List Nat} (hs : List Nat) (hj : j ∈ js) (hd : slot w j ≤ d)
    (hn : d + n ≤ slot w j + 8 * (w + 2)) : ∃ r' ∈ rg w js hs, r'.1 ≤ d ∧ d + n ≤ r'.1 + r'.2 :=
  ⟨_, rg_mem_arr hs hj, hd, hn⟩

theorem rg_cover_hdr {w i : Nat} (js : List Nat) {hs : List Nat} (hi : i ∈ hs) :
    ∃ r' ∈ rg w js hs, r'.1 ≤ 8 * i ∧ 8 * i + 8 ≤ r'.1 + r'.2 :=
  ⟨_, rg_mem_hdr js hi, Nat.le_refl _, Nat.le_refl _⟩

theorem Ws.congrG {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {js hs : List Nat}
    (hf : Frm B (rg w js hs) s.mem t.mem) (hhs : ∀ i ∈ hs, rSlot i = true) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs) : Ws t B Z w :=
  h.congrR hf (rg_rmut hhs) k hr

end VG.Proof.Rsa.X86_64
