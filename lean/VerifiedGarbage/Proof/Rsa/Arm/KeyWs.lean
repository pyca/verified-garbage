module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Mont.Words32
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The working space of the RSA key operations on ARMv7

`Ws s B Z w N`: `r7`, `r8` and `r9` hold the stride, the base `B` and `w`,
and the working space (`Z` bytes at `B`, `N` arrays after the header) is
writable. `num m B w j` is the number in array `j`, `slot m B d` the word at
byte `d` of the header. `Keep B w js ds m m'`: `m'` is `m` but on the arrays
`js` and the header words `ds`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- The stride. -/
abbrev S (w : Nat) : Nat := 4 * (w + 2)

/-- The offset of array `j`. -/
abbrev arr (w j : Nat) : Nat := hdr + j * S w

/-- The number in array `j`. -/
abbrev num (m : Mem) (B : BitVec 32) (w j : Nat) : Nat := val32 m (State.addr B) (arr w j) w

/-- The word at byte `d`. -/
abbrev slot (m : Mem) (B : BitVec 32) (d : Nat) : Nat := w32 m (State.addr B) d

structure Ws (s : State) (B : BitVec 32) (Z w N : Nat) : Prop where
  nowrap : B.toNat + Z ≤ 2 ^ 32
  writable : (⟨State.addr B, Z⟩ : Region) ∈ s.wr
  fits : arr w N ≤ Z
  wpos : 0 < w
  wle : w ≤ 256
  r7 : s.gpr .r7 = BitVec.ofNat 32 (S w)
  r8 : s.gpr .r8 = B
  r9 : s.gpr .r9 = BitVec.ofNat 32 w

theorem Ws.of {s t : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N)
    (e7 : t.gpr .r7 = s.gpr .r7) (e8 : t.gpr .r8 = s.gpr .r8) (e9 : t.gpr .r9 = s.gpr .r9)
    (wr : t.wr = s.wr) : Ws t B Z w N :=
  ⟨h.nowrap, wr ▸ h.writable, h.fits, h.wpos, h.wle, e7.trans h.r7, e8.trans h.r8, e9.trans h.r9⟩

theorem Ws.rest {s t : State} {B : BitVec 32} {Z w N : Nat} {ws : List Reg} (h : Ws s B Z w N)
    (r : Rest ws s t) (h7 : .r7 ∉ ws := by decide) (h8 : .r8 ∉ ws := by decide)
    (h9 : .r9 ∉ ws := by decide) : Ws t B Z w N :=
  h.of (r.gpr _ h7) (r.gpr _ h8) (r.gpr _ h9) r.wr

theorem Ws.of_upd {s t : State} {B : BitVec 32} {Z w N : Nat} {r : Reg} {v : BitVec 32}
    (h : Ws s B Z w N) (u : Upd s t r v) (h7 : r ≠ .r7) (h8 : r ≠ .r8) (h9 : r ≠ .r9) :
    Ws t B Z w N :=
  h.of (u.other _ h7.symm) (u.other _ h8.symm) (u.other _ h9.symm) u.wr

theorem Ws.of_mupd {s t : State} {B : BitVec 32} {Z w N : Nat} {m : Mem}
    (h : Ws s B Z w N) (u : Mupd s t m) : Ws t B Z w N :=
  h.of (by rw [u.gpr]) (by rw [u.gpr]) (by rw [u.gpr]) u.wr

/-! ## Offsets -/

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

theorem Ws.arr_fit {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    arr w j + S w ≤ Z :=
  Nat.le_trans (arr_end hj) h.fits

theorem Ws.fit64 {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    arr w j + S w ≤ 2 ^ 64 := by
  have := h.arr_fit hj; have := h.nowrap; omega

theorem Ws.hdr_le {s : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N) : hdr ≤ Z :=
  Nat.le_trans (Nat.le_add_right _ _) h.fits

/-- The address `B + d` within the working space. -/
theorem Ws.addr {s : State} {B : BitVec 32} {Z w N d : Nat} (h : Ws s B Z w N) (hd : d < Z) :
    State.addr (B + BitVec.ofNat 32 d) = off (State.addr B) d :=
  VG.Arm.addr_add (by have := h.nowrap; omega)

theorem Ws.write {s : State} {B : BitVec 32} {Z w N d : Nat} (h : Ws s B Z w N) (hd : d + 4 ≤ Z) :
    InRegions s.wr (off (State.addr B) d) 4 :=
  ⟨_, h.writable, Offset.contains_base _ hd (by have := h.nowrap; omega)⟩

theorem Ws.read {s : State} {B : BitVec 32} {Z w N d : Nat} (h : Ws s B Z w N) (hd : d + 4 ≤ Z) :
    InRegions (s.rd ++ s.wr) (off (State.addr B) d) 4 := by
  obtain ⟨R, hR, hsub⟩ := h.write hd
  exact ⟨R, List.mem_append_right _ hR, hsub⟩

/-! ## Array addresses -/

theorem encodable_lt {n : Nat} (h : n < 256) : encodable (BitVec.ofNat 32 n) = true :=
  List.any_eq_true.2 ⟨0, by simp, by
    have h0 : (BitVec.ofNat 32 n).rotateLeft (2 * 0) = BitVec.ofNat 32 n := by ext i; simp
    simpa only [h0, decide_eq_true_eq, BitVec.toNat_ofNat] using (by omega : n % 2 ^ 32 < 256)⟩

theorem ptr_val (B : BitVec 32) (j S : Nat) :
    BitVec.ofNat 32 j * BitVec.ofNat 32 S + B + BitVec.ofNat 32 hdr = B + BitVec.ofNat 32 (hdr + j * S) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_mul]
  ac_rfl

/-- `ptr r j`: `r` holds the address of array `j`. -/
theorem ptr_ok {s : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N) {r : Reg}
    (hr : r ∉ [.r7, .r8, .r9]) {j : Nat} (hj : j < 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = B + BitVec.ofNat 32 (arr w j) → Rest [r] s t → t.mem = s.mem →
      Ws t B Z w N → WP isa (.block rest) t Q) :
    WP isa (.block (ptr r j ++ rest)) s Q := by
  have r7 : r ≠ .r7 := fun e => hr (by simp [e])
  have r8 : r ≠ .r8 := fun e => hr (by simp [e])
  have r9 : r ≠ .r9 := fun e => hr (by simp [e])
  unfold ptr
  refine wp_mov (op2_imm (encodable_lt hj)) fun s1 u1 => ?_
  refine wp_mul fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun t u4 => ?_
  have rest : Rest [r] s t :=
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  refine k t ?_ rest (by rw [u4.mem, u3.mem, u2.mem, u1.mem]) (h.rest rest
    (by simpa using r7.symm) (by simpa using r8.symm) (by simpa using r9.symm))
  rw [u4.gpr, dpVal, u3.gpr, dpVal, u2.gpr, u1.gpr, u2.other .r8 r8.symm, u1.other .r8 r8.symm,
    u1.other .r7 r7.symm, h.r7, h.r8]
  exact ptr_val _ _ _

/-! ## Frames -/

/-- The bytes of the arrays `js` and the header words `ds`. -/
def ranges (w : Nat) (js ds : List Nat) : List (Nat × Nat) :=
  js.map (fun j => (arr w j, S w)) ++ ds.map (fun d => (d, 4))

/-- `m'` is `m` but on the arrays `js` and the header words `ds`. -/
def Keep (B : BitVec 32) (w : Nat) (js ds : List Nat) (m m' : Mem) : Prop :=
  Outs (State.addr B) (ranges w js ds) m m'

theorem Keep.refl (B : BitVec 32) (w : Nat) (js ds : List Nat) (m : Mem) : Keep B w js ds m m :=
  Outs.refl _ _ _

theorem Keep.trans {B : BitVec 32} {w : Nat} {js ds : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Keep B w js ds m₁ m₂) (h₂ : Keep B w js ds m₂ m₃) : Keep B w js ds m₁ m₃ :=
  Outs.trans h₁ h₂

theorem Keep.mono {B : BitVec 32} {w : Nat} {js ds js' ds' : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') (hj : ∀ j ∈ js, j ∈ js' := by simp)
    (hd : ∀ d ∈ ds, d ∈ ds' := by simp) : Keep B w js' ds' m m' := by
  refine Outs.mono h fun r hr => ?_
  simp only [ranges, List.mem_append, List.mem_map] at hr ⊢
  rcases hr with ⟨j, hj', rfl⟩ | ⟨d, hd', rfl⟩
  · exact .inl ⟨j, hj j hj', rfl⟩
  · exact .inr ⟨d, hd d hd', rfl⟩

/-- Two frames, each widened to the union. -/
theorem Keep.join {B : BitVec 32} {w : Nat} {js₁ ds₁ js₂ ds₂ js ds : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Keep B w js₁ ds₁ m₁ m₂) (h₂ : Keep B w js₂ ds₂ m₂ m₃)
    (hj₁ : ∀ j ∈ js₁, j ∈ js := by simp) (hd₁ : ∀ d ∈ ds₁, d ∈ ds := by simp)
    (hj₂ : ∀ j ∈ js₂, j ∈ js := by simp) (hd₂ : ∀ d ∈ ds₂, d ∈ ds := by simp) :
    Keep B w js ds m₁ m₃ :=
  (h₁.mono hj₁ hd₁).trans (h₂.mono hj₂ hd₂)

theorem Keep.of_arr {B : BitVec 32} {w o n d : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside (State.addr B) (arr w o + d) n m m') (hn : d + n ≤ S w) (ho : o ∈ js) :
    Keep B w js ds m m' := by
  intro x hx
  have := hx (arr w o, S w) (by simp only [ranges, List.mem_append, List.mem_map]; exact .inl ⟨o, ho, rfl⟩)
  exact h x (by omega)

theorem Keep.of_slot {B : BitVec 32} {w e : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside (State.addr B) e 4 m m') (he : e ∈ ds) : Keep B w js ds m m' := by
  intro x hx
  have := hx (e, 4) (by simp only [ranges, List.mem_append, List.mem_map]; exact .inr ⟨e, he, rfl⟩)
  exact h x this

/-- An array outside the frame. -/
theorem Keep.num {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) : num m' B w j = num m B w j := by
  have hS : 4 * w ≤ S w := by simp only [S]; omega
  refine Outs.val32 h (fun r hr => ?_) (by omega)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj k hk); dsimp only; omega
  · have := hd d hd'; have : hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega

/-- A word of an array outside the frame. -/
theorem Keep.word {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {j i : Nat} (hi : 4 * i + 4 ≤ S w) (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    w32 m' (State.addr B) (arr w j + 4 * i) = w32 m (State.addr B) (arr w j + 4 * i) := by
  have := Outs.val32 (k := 1) (d := arr w j + 4 * i) h (fun r hr => ?_) (by omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj k hk); dsimp only; omega
  · have := hd d hd'; have : hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega

/-- A header word outside the frame. -/
theorem Keep.slot {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {e : Nat} (he : e + 4 ≤ hdr) (hd : ∀ d ∈ ds, e + 4 ≤ d ∨ d + 4 ≤ e) :
    slot m' B e = slot m B e := by
  have := Outs.val32 (k := 1) (d := e) h (fun r hr => ?_) (by simp only [hdr] at he; omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have : hdr ≤ arr w k := Nat.le_add_right _ _; dsimp only; omega
  · exact hd d hd'

/-- Memory outside the working space. -/
theorem Keep.out {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {Z : Nat} (hj : ∀ j ∈ js, arr w j + S w ≤ Z) (hd : ∀ d ∈ ds, d + 4 ≤ Z)
    {x : Addr} (hx : Z ≤ ofs (State.addr B) x) : m' x = m x := by
  refine h x fun r hr => ?_
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := hj k hk; dsimp only; omega
  · have := hd d hd'; dsimp only; omega

/-! ## Header words -/

theorem slot_addr {s : State} {B : BitVec 32} {Z w N d : Nat} (h : Ws s B Z w N) (hd : d < Z) :
    State.addr (s.gpr .r8 + BitVec.ofNat 32 d) = off (State.addr B) d := by
  rw [h.r8]; exact h.addr hd

/-- `ldr t, [r8, #d]`. -/
theorem wp_ldrSlot {s : State} {B : BitVec 32} {Z w N d : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ hdr) {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (s.mem.readW (off (State.addr B) d) 32) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldr t .r8 d :: rest)) s Q := by
  have := h.hdr_le
  exact wp_ldr (by simp only [hdr] at hd; omega) (slot_addr h (by omega)) (h.read (by omega)) k

/-- `str t, [r8, #d]`. -/
theorem wp_strSlot {s : State} {B : BitVec 32} {Z w N d : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ hdr) {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (off (State.addr B) d) (s.gpr t)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.str t .r8 d :: rest)) s Q := by
  have := h.hdr_le
  exact wp_str (by simp only [hdr] at hd; omega) (slot_addr h (by omega)) (h.write (by omega)) k

theorem slot_write_self (m : Mem) (B : BitVec 32) (d : Nat) (v : BitVec 32) :
    slot (m.writeW (off (State.addr B) d) v) B d = v.toNat :=
  w32_write_self m _ d v

theorem keep_write {B : BitVec 32} {w d : Nat} {js ds : List Nat} (m : Mem) (v : BitVec 32)
    (hd : d ∈ ds) (fit : d + 4 ≤ 2 ^ 64) : Keep B w js ds m (m.writeW (off (State.addr B) d) v) :=
  Keep.of_slot (writeW32_outside m _ v fit) hd

end VG.Proof.Rsa.Arm.Keys
