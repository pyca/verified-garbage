module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.Arm.RowState
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Bignum.Arm.SubState
public import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasState
public import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem

/-! # The working space of `inverse` on ARMv7: arrays of the stride `S W`, numbers of `k` words

`Gk s B Z W k N`: `Ws` with `r9 = k ≤ W` in place of `W`. `nk m B W j L` is the number in the
low `L` words of array `j`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm (Rest Upd)
open VG.Proof.Bignum.Arm (SubCtx SelectCtx RowCtx ZeroCtx)

structure Gk (s : State) (B : BitVec 32) (Z W k N : Nat) : Prop where
  nowrap : B.toNat + Z ≤ 2 ^ 32
  writable : (⟨State.addr B, Z⟩ : Region) ∈ s.wr
  fits : arr W N ≤ Z
  kpos : 0 < k
  kle : k ≤ W
  wle : W ≤ 1024
  r7 : s.gpr .r7 = BitVec.ofNat 32 (S W)
  r8 : s.gpr .r8 = B
  r9 : s.gpr .r9 = BitVec.ofNat 32 k

/-- The low `L` words of array `j`. -/
abbrev nk (m : Mem) (B : BitVec 32) (W j L : Nat) : Nat := val32 m (State.addr B) (arr W j) L

theorem Gk.of {s t : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N)
    (e7 : t.gpr .r7 = s.gpr .r7) (e8 : t.gpr .r8 = s.gpr .r8) (e9 : t.gpr .r9 = s.gpr .r9)
    (wr : t.wr = s.wr) : Gk t B Z W k N :=
  ⟨h.nowrap, wr ▸ h.writable, h.fits, h.kpos, h.kle, h.wle, e7.trans h.r7, e8.trans h.r8, e9.trans h.r9⟩

theorem Gk.rest {s t : State} {B : BitVec 32} {Z W k N : Nat} {ws : List Reg} (h : Gk s B Z W k N)
    (r : Rest ws s t) (h7 : .r7 ∉ ws := by decide) (h8 : .r8 ∉ ws := by decide)
    (h9 : .r9 ∉ ws := by decide) : Gk t B Z W k N :=
  h.of (r.gpr _ h7) (r.gpr _ h8) (r.gpr _ h9) r.wr

theorem Gk.arr_fit {s : State} {B : BitVec 32} {Z W k N j : Nat} (h : Gk s B Z W k N) (hj : j < N) :
    arr W j + S W ≤ Z := Nat.le_trans (arr_end hj) h.fits

theorem Gk.fit64 {s : State} {B : BitVec 32} {Z W k N j : Nat} (h : Gk s B Z W k N) (hj : j < N) :
    arr W j + S W ≤ 2 ^ 64 := by
  have := h.arr_fit hj; have := h.nowrap; omega

theorem Gk.addr {s : State} {B : BitVec 32} {Z W k N d : Nat} (h : Gk s B Z W k N) (hd : d < Z) :
    State.addr (B + BitVec.ofNat 32 d) = off (State.addr B) d :=
  VG.Arm.addr_add (by have := h.nowrap; omega)

theorem Gk.write {s : State} {B : BitVec 32} {Z W k N d : Nat} (h : Gk s B Z W k N) (hd : d + 4 ≤ Z) :
    InRegions s.wr (off (State.addr B) d) 4 :=
  ⟨_, h.writable, Offset.contains_base _ hd (by have := h.nowrap; omega)⟩

theorem Gk.read {s : State} {B : BitVec 32} {Z W k N d : Nat} (h : Gk s B Z W k N) (hd : d + 4 ≤ Z) :
    InRegions (s.rd ++ s.wr) (off (State.addr B) d) 4 := by
  obtain ⟨R, hR, hsub⟩ := h.write hd
  exact ⟨R, List.mem_append_right _ hR, hsub⟩

/-- `ptr r j` under `Gk`. -/
theorem Gk.ptr_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) {r : Reg}
    (hr : r ∉ [.r7, .r8, .r9]) {j : Nat} (hj : j < 256) {rest : List Instr} {Q : State → Prop}
    (kk : ∀ t, t.gpr r = B + BitVec.ofNat 32 (arr W j) → Rest [r] s t → t.mem = s.mem →
      Gk t B Z W k N → WP isa (.block rest) t Q) :
    WP isa (.block (ptr r j ++ rest)) s Q := by
  have r7 : r ≠ .r7 := fun e => hr (by simp [e])
  have r8 : r ≠ .r8 := fun e => hr (by simp [e])
  have r9 : r ≠ .r9 := fun e => hr (by simp [e])
  refine ptr_regs_ok r7 r8 hj h.r7 h.r8 fun t p rest mem => ?_
  exact kk t p rest mem (h.rest rest (by simpa using r7.symm)
    (by simpa using r8.symm) (by simpa using r9.symm))

/-- Three pointers. -/
theorem Gk.ptr3_ok {s : State} {B : BitVec 32} {Z W k N o a b : Nat} (h : Gk s B Z W k N)
    (ho : o < 256) (ha : a < 256) (hb : b < 256) {rest : List Instr} {Q : State → Prop}
    (kk : ∀ t, t.gpr .r0 = B + BitVec.ofNat 32 (arr W o) → t.gpr .r10 = B + BitVec.ofNat 32 (arr W a) →
      t.gpr .r12 = B + BitVec.ofNat 32 (arr W b) → Rest [.r0, .r10, .r12] s t → t.mem = s.mem →
      Gk t B Z W k N → WP isa (.block rest) t Q) :
    WP isa (.block (ptr .r0 o ++ ptr .r10 a ++ ptr .r12 b ++ rest)) s Q := by
  simp only [List.append_assoc]
  refine h.ptr_ok (by decide) ho fun s1 p1 r1 m1 h1 => ?_
  refine h1.ptr_ok (by decide) ha fun s2 p2 r2 m2 h2 => ?_
  refine h2.ptr_ok (by decide) hb fun t p3 r3 m3 h3 => ?_
  refine kk t ?_ ?_ p3 ((r1.mono (by simp)).trans ((r2.mono (by simp)).trans (r3.mono (by simp))))
    (m3.trans (m2.trans m1)) h3
  · rw [r3.gpr _ (by decide), r2.gpr _ (by decide), p1]
  · rw [r3.gpr _ (by decide), p2]

/-! ## Contexts of the word loops, for arrays and `L ≤ W + 1` words -/

theorem Gk.subCtx {s : State} {B : BitVec 32} {Z W k N o a b L : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hoa : o ≠ a) (hob : o ≠ b) (hL : L ≤ W + 2) :
    SubCtx s B Z (arr W o) (arr W a) (arr W b) L := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have da := arr_disj (w := W) hoa
  have db := arr_disj (w := W) hob
  have hS : S W = 4 * (W + 2) := rfl
  exact ⟨h.nowrap, by omega, by omega, by omega, by omega, by omega, h.writable⟩

theorem Gk.selCtx {s : State} {B : BitVec 32} {Z W k N o a b L : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hL : L ≤ W + 2) :
    SelectCtx s B Z (arr W o) (arr W a) (arr W b) L := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have hS : S W = 4 * (W + 2) := rfl
  refine ⟨h.nowrap, by omega, by omega, by omega, ?_, ?_, h.writable⟩
  · by_cases e : o = a
    · exact .inr (.inr (by rw [e]))
    · have := arr_disj (w := W) e; omega
  · by_cases e : o = b
    · exact .inr (.inr (by rw [e]))
    · have := arr_disj (w := W) e; omega

theorem Gk.rowCtx {s : State} {B : BitVec 32} {Z W k N o b L : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (hb : b < N) (hob : o ≠ b) (hL : L ≤ W + 2) :
    RowCtx s B Z (arr W o) (arr W b) L := by
  have fo := h.arr_fit ho
  have fb := h.arr_fit hb
  have db := arr_disj (w := W) hob
  have hS : S W = 4 * (W + 2) := rfl
  exact ⟨h.nowrap, by omega, by omega, by omega, h.writable⟩

theorem Gk.zeroCtx {s : State} {B : BitVec 32} {Z W k N o L : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (hL : L ≤ W + 2) : ZeroCtx s B Z (arr W o) L := by
  have fo := h.arr_fit ho
  have hS : S W = 4 * (W + 2) := rfl
  exact ⟨h.nowrap, by omega, ⟨_, h.writable, Region.contains_self _ _⟩⟩

/-! ## Frames at a width -/

/-- The low `L ≤ W + 2` words of an array outside the frame. -/
theorem Keep.nk {B : BitVec 32} {W : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B W js ds m m') {j L : Nat} (hL : L ≤ W + 2) (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (fit : arr W j + S W ≤ 2 ^ 64) : nk m' B W j L = nk m B W j L := by
  refine Outs.val32 h (fun r hr => ?_) (by simp only [S] at fit; omega)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := W) (hj k hk); dsimp only; simp only [S] at *; omega
  · have := hd d hd'; have : hdr ≤ arr W j := Nat.le_add_right _ _; dsimp only; omega

end VG.Proof.Rsa.Arm.Inv
