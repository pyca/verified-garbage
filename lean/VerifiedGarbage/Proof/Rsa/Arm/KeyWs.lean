module

import VerifiedGarbage.Proof.Rsa.KeyWorkspace
public import VerifiedGarbage.Impl.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

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
  wle : w ≤ 1024
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

theorem arr_succ (w j : Nat) : arr w (j + 1) = arr w j + S w :=
  VG.Proof.Rsa.KeyWorkspace.arr_succ w j

theorem arr_mono {w j k : Nat} (h : j ≤ k) : arr w j ≤ arr w k :=
  VG.Proof.Rsa.KeyWorkspace.arr_mono h

theorem arr_end {w j k : Nat} (h : j < k) : arr w j + S w ≤ arr w k :=
  VG.Proof.Rsa.KeyWorkspace.arr_end h

theorem arr_disj {w j k : Nat} (h : j ≠ k) : arr w j + S w ≤ arr w k ∨ arr w k + S w ≤ arr w j :=
  VG.Proof.Rsa.KeyWorkspace.arr_disj h

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

/-- Address arithmetic from the two public layout registers. -/
theorem ptr_regs_ok {s : State} {B : BitVec 32} {stride : Nat} {r : Reg}
    (r7 : r ≠ .r7) (r8 : r ≠ .r8) {j : Nat} (hj : j < 256)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 stride) (h8 : s.gpr .r8 = B)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = B + BitVec.ofNat 32 (hdr + j * stride) →
      Rest [r] s t → t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (ptr r j ++ rest)) s Q := by
  cases j with
  | zero =>
    unfold ptr
    refine wp_dp (op2_imm (by decide)) fun t u => k t ?_ (u.rest (by simp)) u.mem
    rw [u.gpr, dpVal, h8]
    simp only [Nat.zero_mul, Nat.add_zero]
  | succ j =>
    cases j with
    | zero =>
      unfold ptr
      refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
      refine wp_dp (op2_imm (by decide)) fun t u2 => k t ?_
        ((u1.rest (by simp)).trans (u2.rest (by simp))) (u2.mem.trans u1.mem)
      rw [u2.gpr, dpVal, u1.gpr, dpVal, h7, h8]
      simp only [Nat.zero_add, Nat.one_mul]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm stride hdr]
    | succ j =>
      unfold ptr
      refine wp_mov (op2_imm (encodable_lt hj)) fun s1 u1 => ?_
      let s2 := s1.setReg r (s1.gpr r * s1.gpr .r7 + s1.gpr .r8)
      have u2 : Upd s1 s2 r (s1.gpr r * s1.gpr .r7 + s1.gpr .r8) := Upd.setReg _ _ _
      refine VG.Proof.X25519.Arm.WP.cons rfl ?_
      refine wp_dp (op2_imm (by decide)) fun t u3 => k t ?_
        ((u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp))))
        (u3.mem.trans (u2.mem.trans u1.mem))
      rw [u3.gpr, dpVal, u2.gpr, u1.gpr, u1.other .r8 r8.symm,
        u1.other .r7 r7.symm, h7, h8]
      exact ptr_val _ _ _

/-- `ptr r j`: `r` holds the address of array `j`. -/
theorem ptr_ok {s : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N) {r : Reg}
    (hr : r ∉ [.r7, .r8, .r9]) {j : Nat} (hj : j < 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = B + BitVec.ofNat 32 (arr w j) → Rest [r] s t → t.mem = s.mem →
      Ws t B Z w N → WP isa (.block rest) t Q) :
    WP isa (.block (ptr r j ++ rest)) s Q := by
  have r7 : r ≠ .r7 := fun e => hr (by simp [e])
  have r8 : r ≠ .r8 := fun e => hr (by simp [e])
  have r9 : r ≠ .r9 := fun e => hr (by simp [e])
  refine ptr_regs_ok r7 r8 hj h.r7 h.r8 fun t p rest mem => ?_
  exact k t p rest mem (h.rest rest (by simpa using r7.symm)
    (by simpa using r8.symm) (by simpa using r9.symm))

/-! ## Frames -/

/-- The bytes of the arrays `js` and the header words `ds`. -/
def ranges (w : Nat) (js ds : List Nat) : List (Nat × Nat) :=
  js.map (fun j => (arr w j, S w)) ++ ds.map (fun d => (d, 4))

/-- `m'` is `m` but on the arrays `js` and the header words `ds`. -/
def Keep (B : BitVec 32) (w : Nat) (js ds : List Nat) (m m' : Mem) : Prop :=
  Outs (State.addr B) (ranges w js ds) m m'

theorem Keep.refl (B : BitVec 32) (w : Nat) (js ds : List Nat) (m : Mem) : Keep B w js ds m m :=
  VG.Proof.Rsa.KeyWorkspace.Keep.refl (State.addr B) w js ds m

theorem Keep.trans {B : BitVec 32} {w : Nat} {js ds : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Keep B w js ds m₁ m₂) (h₂ : Keep B w js ds m₂ m₃) : Keep B w js ds m₁ m₃ :=
  VG.Proof.Rsa.KeyWorkspace.Keep.trans h₁ h₂

theorem Keep.mono {B : BitVec 32} {w : Nat} {js ds js' ds' : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') (hj : ∀ j ∈ js, j ∈ js' := by simp)
    (hd : ∀ d ∈ ds, d ∈ ds' := by simp) : Keep B w js' ds' m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.mono h hj hd

/-- Two frames, each widened to the union. -/
theorem Keep.join {B : BitVec 32} {w : Nat} {js₁ ds₁ js₂ ds₂ js ds : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Keep B w js₁ ds₁ m₁ m₂) (h₂ : Keep B w js₂ ds₂ m₂ m₃)
    (hj₁ : ∀ j ∈ js₁, j ∈ js := by simp) (hd₁ : ∀ d ∈ ds₁, d ∈ ds := by simp)
    (hj₂ : ∀ j ∈ js₂, j ∈ js := by simp) (hd₂ : ∀ d ∈ ds₂, d ∈ ds := by simp) :
    Keep B w js ds m₁ m₃ :=
  VG.Proof.Rsa.KeyWorkspace.Keep.join h₁ h₂ hj₁ hd₁ hj₂ hd₂

theorem Keep.of_arr {B : BitVec 32} {w o n d : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside (State.addr B) (arr w o + d) n m m') (hn : d + n ≤ S w) (ho : o ∈ js) :
    Keep B w js ds m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.of_arr h hn ho

theorem Keep.of_slot {B : BitVec 32} {w e : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside (State.addr B) e 4 m m') (he : e ∈ ds) : Keep B w js ds m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.of_slot h he

/-- An array outside the frame. -/
theorem Keep.num {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) : num m' B w j = num m B w j :=
  VG.Proof.Rsa.KeyWorkspace.Keep.num h hj hd fit

/-- All the words of an array outside the frame. -/
theorem Keep.full {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) :
    val32 m' (State.addr B) (arr w j) (w + 2) = val32 m (State.addr B) (arr w j) (w + 2) :=
  VG.Proof.Rsa.KeyWorkspace.Keep.full h hj hd fit

/-- A word of an array outside the frame. -/
theorem Keep.word {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {j i : Nat} (hi : 4 * i + 4 ≤ S w) (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    w32 m' (State.addr B) (arr w j + 4 * i) = w32 m (State.addr B) (arr w j + 4 * i) :=
  VG.Proof.Rsa.KeyWorkspace.Keep.word h hi hj hd fit

/-- A header word outside the frame. -/
theorem Keep.slot {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {e : Nat} (he : e + 4 ≤ hdr) (hd : ∀ d ∈ ds, e + 4 ≤ d ∨ d + 4 ≤ e) :
    slot m' B e = slot m B e :=
  VG.Proof.Rsa.KeyWorkspace.Keep.slot h he hd

/-- Memory outside the working space. -/
theorem Keep.out {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {Z : Nat} (hj : ∀ j ∈ js, arr w j + S w ≤ Z) (hd : ∀ d ∈ ds, d + 4 ≤ Z)
    {x : Addr} (hx : Z ≤ ofs (State.addr B) x) : m' x = m x :=
  VG.Proof.Rsa.KeyWorkspace.Keep.out h hj hd hx

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
