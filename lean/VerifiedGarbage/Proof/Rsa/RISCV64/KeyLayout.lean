module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyWs
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The working space of the RSA key operations on RISC-V

The 64-bit counterpart of `Proof/Rsa/KeyWorkspace.lean`: after a header of
`hdr = 256` bytes, array `j` is at byte `arr w j = hdr + j S` with the stride
`S = 8 (w + 2)`, and holds the number `num m B w j` of its first `w` words;
a slot is the word `slot m B d` at byte `d` of the header. `Frame B w js ds
m m'` says `m'` is `m` but on the arrays `js` and the slots `ds`.

`Ws s B Z w N`: `s9`, `s10` and `s11` hold `w`, the stride and the base `B`,
and the working space (`Z` bytes at `B`, `N` arrays after the header) is
writable (`Scr`). `ptr_ok`: `ptr r j` puts the address of array `j` in `r`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr ptrs)

abbrev hdr : Nat := VG.Impl.Rsa.RISCV64.Keys.hdr
abbrev S (w : Nat) : Nat := 8 * (w + 2)
abbrev arr (w j : Nat) : Nat := hdr + j * S w
abbrev num (m : Mem) (B : Addr) (w j : Nat) : Nat := wordsVal m B (arr w j) w
abbrev slot (m : Mem) (B : Addr) (d : Nat) : Nat := (word m B d).toNat

theorem hdr_eq : hdr = 256 := rfl

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

theorem arr_al (w j : Nat) : arr w j % 8 = 0 := by
  simp only [arr, hdr_eq, S]
  rw [Nat.mul_comm j, Nat.mul_assoc]; omega_arith

theorem hdr_le_arr (w j : Nat) : hdr ≤ arr w j := Nat.le_add_right _ _

/-! ## Frames -/

/-- The bytes of the arrays `js` and the slots `ds`. -/
def ranges (w : Nat) (js ds : List Nat) : List (Nat × Nat) :=
  js.map (fun j => (arr w j, S w)) ++ ds.map (fun d => (d, 8))

/-- `m'` is `m` but on the arrays `js` and the slots `ds`. -/
def Frame (B : Addr) (w : Nat) (js ds : List Nat) (m m' : Mem) : Prop :=
  Outs B (ranges w js ds) m m'

theorem Frame.refl (B : Addr) (w : Nat) (js ds : List Nat) (m : Mem) : Frame B w js ds m m :=
  Outs.refl _ _ _

theorem Frame.trans {B : Addr} {w : Nat} {js ds : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Frame B w js ds m₁ m₂) (h₂ : Frame B w js ds m₂ m₃) : Frame B w js ds m₁ m₃ :=
  Outs.trans h₁ h₂

theorem Frame.mono {B : Addr} {w : Nat} {js ds js' ds' : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') (hj : ∀ j ∈ js, j ∈ js' := by simp)
    (hd : ∀ d ∈ ds, d ∈ ds' := by simp) : Frame B w js' ds' m m' := by
  refine Outs.mono h fun r hr => ?_
  simp only [ranges, List.mem_append, List.mem_map] at hr ⊢
  rcases hr with ⟨j, hj', rfl⟩ | ⟨d, hd', rfl⟩
  · exact .inl ⟨j, hj j hj', rfl⟩
  · exact .inr ⟨d, hd d hd', rfl⟩

/-- Two frames, each widened to the union. -/
theorem Frame.join {B : Addr} {w : Nat} {js₁ ds₁ js₂ ds₂ js ds : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Frame B w js₁ ds₁ m₁ m₂) (h₂ : Frame B w js₂ ds₂ m₂ m₃)
    (hj₁ : ∀ j ∈ js₁, j ∈ js := by simp) (hd₁ : ∀ d ∈ ds₁, d ∈ ds := by simp)
    (hj₂ : ∀ j ∈ js₂, j ∈ js := by simp) (hd₂ : ∀ d ∈ ds₂, d ∈ ds := by simp) :
    Frame B w js ds m₁ m₃ :=
  (h₁.mono hj₁ hd₁).trans (h₂.mono hj₂ hd₂)

/-- Bytes changed only within an array. -/
theorem Frame.of_arr {B : Addr} {w o n d : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside B (arr w o + d) n m m') (hn : d + n ≤ S w) (ho : o ∈ js) :
    Frame B w js ds m m' := by
  intro x hx
  have := hx (arr w o, S w) (by simp only [ranges, List.mem_append, List.mem_map]; exact .inl ⟨o, ho, rfl⟩)
  exact h x (by omega_arith)

/-- Bytes changed only within a slot. -/
theorem Frame.of_slot {B : Addr} {w e : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside B e 8 m m') (he : e ∈ ds) : Frame B w js ds m m' := by
  intro x hx
  have := hx (e, 8) (by simp only [ranges, List.mem_append, List.mem_map]; exact .inr ⟨e, he, rfl⟩)
  exact h x this

/-- The `k` words at `d`, apart from every range that changed. -/
theorem Outs.wordsVal {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d k : Nat} (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    VG.Proof.Mont.wordsVal m' base d k = VG.Proof.Mont.wordsVal m base d k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [VG.Proof.Mont.wordsVal]
    have hw : word m' base d = word m base d :=
      Mem.readW_congr fun i hi => h _ fun r hr => by
        have := hd r hr
        rw [ofs_off base (by omega_arith)]; omega_arith
    rw [hw, ih (fun r hr => by have := hd r hr; omega_arith) (by omega_arith)]

/-- The `k` words at `d`, apart from the frame's ranges. -/
theorem Frame.words {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') {d k : Nat}
    (hj : ∀ j ∈ js, d + 8 * k ≤ arr w j ∨ arr w j + S w ≤ d)
    (hd : ∀ e ∈ ds, d + 8 * k ≤ e ∨ e + 8 ≤ d) (fit : d + 8 * k ≤ 2 ^ 64) :
    wordsVal m' B d k = wordsVal m B d k := by
  refine Outs.wordsVal h (fun r hr => ?_) fit
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj', rfl⟩ | ⟨e, he, rfl⟩
  · exact hj j hj'
  · exact hd e he

/-- A number of an array outside the frame. -/
theorem Frame.num {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 8 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) : num m' B w j = num m B w j := by
  have hS : S w = 8 * (w + 2) := rfl
  exact h.words (fun k hk => by have := arr_disj (w := w) (hj k hk); omega_arith)
    (fun d hd' => by have := hd d hd'; have := hdr_le_arr w j; omega_arith) (by omega_arith)

/-- All the `w + 2` words of an array outside the frame. -/
theorem Frame.full {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 8 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) :
    wordsVal m' B (arr w j) (w + 2) = wordsVal m B (arr w j) (w + 2) := by
  have hS : S w = 8 * (w + 2) := rfl
  exact h.words (fun k hk => by have := arr_disj (w := w) (hj k hk); omega_arith)
    (fun d hd' => by have := hd d hd'; have := hdr_le_arr w j; omega_arith) (by omega_arith)

/-- A word of an array outside the frame. -/
theorem Frame.word {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') {j i : Nat} (hi : i < w + 2) (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 8 ≤ hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    word m' B (arr w j + 8 * i) = word m B (arr w j + 8 * i) := by
  have hS : S w = 8 * (w + 2) := rfl
  have := h.words (d := arr w j + 8 * i) (k := 1)
    (fun k hk => by have := arr_disj (w := w) (hj k hk); omega_arith)
    (fun d hd' => by have := hd d hd'; have := hdr_le_arr w j; omega_arith) (by omega_arith)
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at this
  exact BitVec.eq_of_toNat_eq this

/-- A slot outside the frame. -/
theorem Frame.slot {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') {e : Nat} (he : e + 8 ≤ hdr) (hd : ∀ d ∈ ds, e + 8 ≤ d ∨ d + 8 ≤ e) :
    slot m' B e = slot m B e := by
  have := h.words (d := e) (k := 1)
    (fun k _ => by have := hdr_le_arr w k; omega_arith) hd (by simp only [hdr_eq] at he; omega_arith)
  simpa only [wordsVal, Nat.mul_zero, Nat.add_zero] using this

/-- Memory outside the working space. -/
theorem Frame.out {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') {Z : Nat} (hj : ∀ j ∈ js, arr w j + S w ≤ Z) (hd : ∀ d ∈ ds, d + 8 ≤ Z)
    {x : Addr} (hx : Z ≤ ofs B x) : m' x = m x := by
  refine h x fun r hr => ?_
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := hj k hk; dsimp only; omega_arith
  · have := hd d hd'; dsimp only; omega_arith

/-! ## The registers of the working space -/

structure Ws (s : State) (B : Addr) (Z w N : Nat) : Prop where
  scr : Scr s B Z
  fits : arr w N ≤ Z
  wpos : 0 < w
  wle : w ≤ 1024
  s9 : s.gpr .s9 = BitVec.ofNat 64 w
  s10 : s.gpr .s10 = BitVec.ofNat 64 (S w)
  s11 : s.gpr .s11 = B

theorem Ws.of_keep {s t : State} {B : Addr} {Z w N : Nat} {rs : List Reg} (h : Ws s B Z w N)
    (k : Keep rs s t) (h9 : .s9 ∉ rs := by decide) (h10 : .s10 ∉ rs := by decide)
    (h11 : .s11 ∉ rs := by decide) : Ws t B Z w N :=
  ⟨h.scr.congr k.2.2, h.fits, h.wpos, h.wle, (k.gpr h9).trans h.s9, (k.gpr h10).trans h.s10,
    (k.gpr h11).trans h.s11⟩

theorem Ws.nowrap {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) : B.toNat + Z ≤ 2 ^ 64 :=
  h.scr.nowrap

theorem Ws.arr_fit {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    arr w j + S w ≤ Z :=
  Nat.le_trans (arr_end hj) h.fits

theorem Ws.fit64 {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    arr w j + S w ≤ 2 ^ 64 := by
  have := h.arr_fit hj; have := h.nowrap; omega_arith

theorem Ws.hdr_le {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) : hdr ≤ Z :=
  Nat.le_trans (hdr_le_arr _ _) h.fits

/-! ## Array addresses -/

theorem add_ofNat_zero' (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x


theorem ptr_val (B : Addr) (j S : Nat) :
    BitVec.ofNat 64 j * BitVec.ofNat 64 S + B + BitVec.ofNat 64 hdr = off B (hdr + j * S) := by
  simp only [off, BitVec.ofNat_add, BitVec.ofNat_mul]
  ac_rfl

/-- `ptr r j`: `r` holds the address of array `j`. -/
theorem ptr_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) {r : Reg}
    (h10 : r ≠ .s10) (h11 : r ≠ .s11) {j : Nat} (hj : j < 2048) {rest : List Instr}
    {Q : State → Prop} (k : WP isa (.block rest) (s.write r (off B (arr w j))) Q) :
    WP isa (.block (ptr r j ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.of_runBlock ?_
  simp only [ptr, runBlock_cons, runStep_some, runBlock_nil, exec_li_nat hj, exec_mul, exec_add,
    exec_addi_nat (show hdr < 2048 by decide), Option.some.injEq,
    exists_eq_left', gpr_write, ite_true, Ne.symm h10, Ne.symm h11, ite_false, write_write, h.s10,
    h.s11, ptr_val]
  exact k

/-- The pointers of three arrays into `t0`, `t1` and `t2`, the rest of a block after them. -/
theorem ptrs_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) {o a b : Nat}
    (ho : o < 2048) (ha : a < 2048) (hb : b < 2048) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .t0 = off B (arr w o) → t.gpr .t1 = off B (arr w a) → t.gpr .t2 = off B (arr w b) →
      Keep [.t0, .t1, .t2] s t → t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (ptrs o a b ++ rest)) s Q := by
  simp only [ptrs, List.append_assoc]
  refine ptr_ok h (by decide) (by decide) ho ?_
  refine ptr_ok (h.of_keep (Keep.write _ _ _)) (by decide) (by decide) ha ?_
  refine ptr_ok ((h.of_keep (Keep.write _ _ _)).of_keep (Keep.write _ _ _)) (by decide) (by decide) hb ?_
  exact k _ (by simp [gpr_write]) (by simp [gpr_write]) (by simp [gpr_write])
    ((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide)) rfl

/-- The pointers of two arrays into `r` and `r'`. -/
theorem ptr2_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) {r r' : Reg}
    (h9 : r ≠ .s9) (h10 : r ≠ .s10) (h11 : r ≠ .s11) (h10' : r' ≠ .s10) (h11' : r' ≠ .s11)
    (hne : r ≠ r') {a b : Nat} (ha : a < 2048) (hb : b < 2048) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = off B (arr w a) → t.gpr r' = off B (arr w b) →
      Keep [r, r'] s t → t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (ptr r a ++ ptr r' b ++ rest)) s Q := by
  rw [List.append_assoc]
  refine ptr_ok h h10 h11 ha ?_
  refine ptr_ok (h.of_keep (Keep.write _ _ _) (by simp [Ne.symm h9]) (by simp [Ne.symm h10])
    (by simp [Ne.symm h11])) h10' h11' hb ?_
  exact k _ (by simp [gpr_write, hne]) (by simp [gpr_write])
    ((Keep.write _ _ _).trans (Keep.write _ _ _)) rfl

/-! ## Bits -/

/-- The exclusive or of two bits. -/
theorem xor_bits {x y : BitVec 64} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x ^^^ y).toNat = (x.toNat + y.toNat) % 2 := by
  rw [BitVec.toNat_xor]
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega_arith) with e | e <;>
    rcases (show y.toNat = 0 ∨ y.toNat = 1 by omega_arith) with f | f <;> rw [e, f] <;> decide

/-! ## Sequences -/

theorem wp_seqs_cons {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop} :
    WP isa (VG.Impl.Rsa.RISCV64.Keys.seqs (c :: l)) s Q ↔
      WP isa c s (fun t => WP isa (VG.Impl.Rsa.RISCV64.Keys.seqs l) t Q) := by
  match l, hl with
  | _ :: _, _ => exact WP.seq_iff

theorem wp_seqs_append {l₁ l₂ : List (Prog isa)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) {s : State}
    {Q : State → Prop} :
    WP isa (VG.Impl.Rsa.RISCV64.Keys.seqs (l₁ ++ l₂)) s Q ↔
      WP isa (VG.Impl.Rsa.RISCV64.Keys.seqs l₁) s (fun t => WP isa (VG.Impl.Rsa.RISCV64.Keys.seqs l₂) t Q) := by
  induction l₁ generalizing s with
  | nil => exact absurd rfl h₁
  | cons c l ih =>
    rcases l with _ | ⟨d, l⟩
    · exact wp_seqs_cons h₂
    · rw [List.cons_append, wp_seqs_cons (by simp), wp_seqs_cons (by simp)]
      exact ⟨fun h => WP.mono h fun t ht => (ih (by simp)).mp ht,
        fun h => WP.mono h fun t ht => (ih (by simp)).mpr ht⟩

end VG.Proof.Rsa.RISCV64.Keys
