module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Calls
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop

/-!
# ML-KEM on RISC-V: addresses, copying bytes and zeroing a polynomial

The steps of the blocks that compute addresses (`wp_polyAddr`, `wp_slotAt`,
`wp_atMul`) and count (`wp_count`), one instruction at a time; and, as on
PPC64LE (`Proof/MlKem/PPC64LE/Loops.lean`): `copy` copies bytes one at a time
(`copyL`: the destination holds the source's bytes, and nothing else
changes), and `zeroPoly` stores zero to every coefficient (`zeroPoly_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.RISCV64.Wp
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Addresses and counts -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_slli {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sll .d d n sh :: is)) s Q :=
  Wp.WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_srli {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .srl .d d n sh :: is)) s Q :=
  Wp.WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_and {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  Wp.WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_or {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  Wp.WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_sw {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (al : a.toNat % 4 = 0) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t n off :: is)) s Q := by
  refine Wp.WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_w ho (by rw [ha]; exact al) (by rw [ha]; exact hout), ha]

theorem wp_mul {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  Wp.WP.cons exec_mul (k _ (Upd.write _ _ _))

end

/-- A register after an update, by cases. -/
theorem _root_.VG.RISCV64.Wp.Upd.gpr_eq {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) (r : Reg) :
    s'.gpr r = if r = d then v else s.gpr r := by
  by_cases e : r = d
  · subst e; rw [ite_eq_left rfl, h.gpr]
  · rw [ite_eq_right e, h.other r e]

/-- Two updates of the same register. -/
theorem Upd.same {s s₁ s₂ : State} {d : Reg} {v₁ v₂ : BitVec 64} (h₁ : Upd s s₁ d v₁) (h₂ : Upd s₁ s₂ d v₂) :
    Upd s s₂ d v₂ :=
  ⟨h₂.gpr, fun r hr => (h₂.other r hr).trans (h₁.other r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem shl10_ofNat {i : Nat} (h : i < 2 ^ 50) : BitVec.ofNat 64 i <<< 10 = BitVec.ofNat 64 (1024 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (a := i) (by omega)]
  omega

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `d ← s11 + oPoly j`. -/
theorem wp_polyAddr {d : Reg} {j : Nat} (hj : j + 2 < 2048) (hd : d ≠ .s11)
    (k : ∀ s', Upd s s' d (s.gpr .s11 + BitVec.ofNat 64 (oPoly j)) → WP isa (.block is) s' Q) :
    WP isa (.block (polyAddr d j ++ is)) s Q := by
  simp only [polyAddr, List.cons_append, List.nil_append]
  refine wp_li hj fun s₁ h₁ => wp_slli (by decide) fun s₂ h₂ => wp_add fun s₃ h₃ => k s₃ ?_
  have u := Upd.same h₁ (Upd.same h₂ h₃)
  refine ⟨?_, u.other, u.mem, u.rd, u.wr, u.sp⟩
  rw [h₃.gpr, h₂.other _ (Ne.symm hd), h₁.other _ (Ne.symm hd), h₂.gpr, h₁.gpr, shl10_ofNat (by omega),
    show oPoly j = 1024 * (j + 2) by unfold oPoly; omega]

/-- `d ← s11 + oPoly j + 1024 i`, with `i` in `c`. -/
theorem wp_slotAt {d c : Reg} {j i : Nat} (hj : j + 2 < 2048) (hi : i + j + 2 < 2 ^ 50) (hd : d ≠ .s11)
    (hc : s.gpr c = BitVec.ofNat 64 i)
    (k : ∀ s', Upd s s' d (s.gpr .s11 + BitVec.ofNat 64 (oPoly j + 1024 * i)) → WP isa (.block is) s' Q) :
    WP isa (.block (slotAt d c j ++ is)) s Q := by
  simp only [slotAt, List.cons_append, List.nil_append]
  refine wp_addi hj fun s₁ h₁ => wp_slli (by decide) fun s₂ h₂ => wp_add fun s₃ h₃ => k s₃ ?_
  have u := Upd.same h₁ (Upd.same h₂ h₃)
  refine ⟨?_, u.other, u.mem, u.rd, u.wr, u.sp⟩
  rw [h₃.gpr, h₂.other _ (Ne.symm hd), h₁.other _ (Ne.symm hd), h₂.gpr, h₁.gpr, hc, ← BitVec.ofNat_add,
    shl10_ofNat (by omega), show oPoly j + 1024 * i = 1024 * (i + (j + 2)) by unfold oPoly; omega]

/-- `s'` is `s` with `d` set to `v` and `t0` changed. -/
structure Upd2 (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → r ≠ .t0 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- `d ← b + m c`. -/
theorem wp_atMul {d b c : Reg} {m : Nat} (hm : m < 2048) (hb : b ≠ .t0) (hc : c ≠ .t0)
    (k : ∀ s', Upd2 s s' d (s.gpr b + s.gpr c * BitVec.ofNat 64 m) → WP isa (.block is) s' Q) :
    WP isa (.block (atMul d b c m ++ is)) s Q := by
  simp only [atMul, List.cons_append, List.nil_append]
  refine wp_li hm fun s₁ h₁ => wp_mul fun s₂ h₂ => wp_add fun s₃ h₃ => k s₃ ?_
  refine ⟨?_, fun r hd ht => by rw [h₃.other r hd, h₂.other r ht, h₁.other r ht],
    by rw [h₃.mem, h₂.mem, h₁.mem], by rw [h₃.rd, h₂.rd, h₁.rd], by rw [h₃.wr, h₂.wr, h₁.wr],
    by rw [h₃.sp, h₂.sp, h₁.sp]⟩
  rw [h₃.gpr, h₂.gpr, h₂.other _ hb, h₁.other _ hb, h₁.gpr, h₁.other _ hc]

/-- `c ← c + 1`, `t0 ← c + 1 - n`. -/
theorem wp_count {c : Reg} {n : Nat} (hn : n ≤ 2048) (hc : c ≠ .t0)
    (k : ∀ s', s'.gpr c = s.gpr c + BitVec.ofNat 64 1 → s'.gpr .t0 = s.gpr c + BitVec.ofNat 64 1 - BitVec.ofNat 64 n →
      (∀ r, r ≠ c → r ≠ .t0 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (count c n ++ is)) s Q := by
  simp only [count, List.cons_append, List.nil_append]
  refine wp_addi (by decide) fun s₁ h₁ => wp_subi hn fun s₂ h₂ => k s₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [h₂.other _ hc, h₁.gpr]
  · rw [h₂.gpr, h₁.gpr]
  · intro r h1 h2; rw [h₂.other r h2, h₁.other r h1]
  · rw [h₂.mem, h₁.mem]
  · rw [h₂.rd, h₁.rd]
  · rw [h₂.wr, h₁.wr]
  · rw [h₂.sp, h₁.sp]

end

theorem setWidth_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt this]

/-! ## `copy` -/

section
variable {s : State} {x y c : BitVec 64}

theorem copyBody_ok (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y) (h5 : s.gpr .a2 = c)
    (ir : InRegions (s.rd ++ s.wr) x 1) (ow : InRegions s.wr y 1) :
    WP isa (.block copyBody) s fun s' =>
      s'.gpr .a0 = x + BitVec.ofNat 64 1 ∧ s'.gpr .a1 = y + BitVec.ofNat 64 1 ∧
      s'.gpr .a2 = c - BitVec.ofNat 64 1 ∧ s'.mem = s.mem.writeW y (s.mem x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  refine wp_lbu (a := x) (by decide) (by rw [h3]; simp) ir fun s₁ h₁ =>
    wp_sb (a := y) (by decide) (by rw [h₁.other _ (by decide), h4]; simp) (by rw [h₁.wr]; exact ow) fun s₂ h₂ =>
    wp_addi (by decide) fun s₃ h₃ => wp_addi (by decide) fun s₄ h₄ => wp_subi (by decide) fun s₅ h₅ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, h₂.gpr, h₁.other _ (by decide), h3]
  · rw [h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), h4]
  · rw [h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), h5]
  · rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.gpr, h₁.mem, setWidth_byte]
  · rw [h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd]
  · rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]
  · rw [h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]
  · obtain ⟨n0, n1, n2, n3, n4, n5⟩ := pres_ne hr
    rw [h₅.other _ n3, h₄.other _ n2, h₃.other _ n1, h₂.gpr, h₁.other _ n4]

end

/-- After copying `k` bytes of `len` from `S` to `D`. -/
structure CopyInv (S D : Addr) (len : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = S + BitVec.ofNat 64 (1 * k)
  a1 : s.gpr .a1 = D + BitVec.ofNat 64 (1 * k)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (len - k)
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨D, len⟩] s₀.mem s.mem
  bytes : ∀ t < k, s.mem (D + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t)

theorem copy_step {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64)
    (hd : (⟨S, len⟩ : Region).Disjoint ⟨D, len⟩)
    (cr : Covers [⟨S, len⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨D, len⟩] s₀.wr)
    {k : Nat} (hk : k < len) {s : State} (h : CopyInv S D len s₀ k s) :
    WP isa (.block copyBody) s fun s' =>
      CopyInv S D len s₀ (k + 1) s' ∧ (s'.gpr .a2 != 0) = decide (k + 1 ≠ len) := by
  have cS : (⟨S, len⟩ : Region).Contains (S + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  have cD : (⟨D, len⟩ : Region).Contains (D + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  have h3 := h.a0; have h4 := h.a1
  rw [Nat.one_mul] at h3 h4
  refine WP.mono (copyBody_ok h3 h4 h.a2 (by rw [h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_singleton_self _, cS⟩)
    (by rw [h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cD⟩))
    fun s' ⟨r3, r4, r5, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, ?_, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r3]; simpa using ptr_succ S 1 k
  · rw [r4]; simpa using ptr_succ D 1 k
  · rw [r5]; exact count_sub hk
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cD
  · rw [m, byte_writeW8 _ _ (by omega) (by omega)]
    have hsrc : s.mem (S + BitVec.ofNat 64 k) = s₀.mem (S + BitVec.ofNat 64 k) :=
      h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd _ cS
    by_cases e : t = k
    · subst e; rw [ite_eq_left rfl, hsrc]
    · rw [ite_eq_right e]; exact h.bytes t (by omega)
  · rw [r5, count_sub hk]; exact count_nz hk hlen

/-- `len` bytes copied from `S` to `D`, with the pointers and the count set
up in `a0`–`a2`. -/
theorem copy_loop {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64) (hl0 : 0 < len)
    (hd : (⟨S, len⟩ : Region).Disjoint ⟨D, len⟩)
    (cr : Covers [⟨S, len⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨D, len⟩] s₀.wr)
    (h3 : s₀.gpr .a0 = S) (h4 : s₀.gpr .a1 = D) (h5 : s₀.gpr .a2 = BitVec.ofNat 64 len) :
    WP isa (.loop (.block copyBody) (.nonzero .a2)) s₀ fun s =>
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Frame [⟨D, len⟩] s₀.mem s.mem ∧ bytesAt s.mem D len = bytesAt s₀.mem S len :=
  wp_loop_nz (CopyInv S D len s₀) hl0 (fun k hk s h => copy_step hlen hd cr cw hk h)
    (fun s h => ⟨h.cs, h.rd, h.wr, h.sp, h.frame, bytesAt_eq (bytesAt_length _ _ _) fun t ht => by
      rw [h.bytes t ht, bytesAt_getElem]⟩)
    ⟨by rw [h3]; simp, by rw [h4]; simp, by rw [h5]; simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun t ht => absurd ht (Nat.not_lt_zero t)⟩

theorem copy_setup {s : State} {sb db : Reg} {so dO len : Nat} (hdb : db ∈ preserved) (hsb : sb ≠ .a0)
    (hse : so < 32768) (hde : dO < 32768) (hle : len < 2048) :
    WP isa (.block (addrOf .a0 sb so ++ addrOf .a1 db dO ++ [.li .a2 len])) s fun s' =>
      Only s s' ∧ s'.gpr .a0 = s.gpr sb + BitVec.ofNat 64 so ∧ s'.gpr .a1 = s.gpr db + BitVec.ofNat 64 dO ∧
      s'.gpr .a2 = BitVec.ofNat 64 len := by
  obtain ⟨-, n1, n2, -, -, -⟩ := pres_ne hdb
  rw [List.append_assoc]
  refine wp_addrOf hsb hse fun s₁ h₁ => wp_addrOf n2 hde fun s₂ h₂ => wp_li hle fun s₃ h₃ =>
    WP.block_nil ⟨(updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans (updOnly h₃ (by decide))),
      ?_, ?_, ?_⟩
  · rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr]
  · rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ n1]
  · rw [h₃.gpr]

/-- `copy`: `len` bytes from offset `so` of buffer `i` (in `sb`) to offset
`dO` of buffer `j` (in `db`). -/
theorem copyL {L : Lay} {s : State} (hL : L.Ok) {sb db : Reg} {so dO len i j : Nat}
    (hdb : db ∈ preserved) (hsb : sb ≠ .a0)
    (gs : s.gpr sb = L.ptr i) (gd : s.gpr db = L.ptr j) (hse : so < 32768) (hde : dO < 32768)
    (hle : len < 2048) (hl0 : 0 < len) (hs : sepB L.sizes (i, so, len) (j, dO, len) = true)
    (ri : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [(j, dO, len)]) s s' ∧ bytesAt s'.mem (L.A j dO) len = bytesAt s.mem (L.A i so) len := by
  refine WP.seq (WP.mono (copy_setup hdb hsb hse hde hle) fun s₁ ⟨o₁, g3, g4, g5⟩ => ?_)
  rw [gs] at g3; rw [gd] at g4
  refine WP.mono (copy_loop (by omega) hl0 (Lay.disj hL hs)
    (by rw [o₁.rd, o₁.wr]; exact Lay.covers ri (sepB_bounds hs).2)
    (by rw [o₁.wr]; exact Lay.covers wj (sepB_bounds (sepB_symm hs)).2) g3 g4 g5)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨(o₁.kept _).trans ⟨cs, sp, rd, wr, fr⟩, ?_⟩
  rw [o₁.mem] at hb; exact hb

/-! ## `zeroPoly` -/

section
variable {s : State} {x c : BitVec 64}

theorem zeroBody_ok (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = 0) (h5 : s.gpr .a2 = c)
    (ow : InRegions s.wr x 4) (ax : x.toNat % 4 = 0) :
    WP isa (.block zeroBody) s fun s' =>
      s'.gpr .a0 = x + BitVec.ofNat 64 4 ∧ s'.gpr .a1 = 0 ∧ s'.gpr .a2 = c - BitVec.ofNat 64 1 ∧
      s'.mem = s.mem.writeW x (0 : BitVec 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  refine wp_sw (a := x) (by decide) (by rw [h3]; simp) ax ow fun s₁ h₁ =>
    wp_addi (by decide) fun s₂ h₂ => wp_subi (by decide) fun s₃ h₃ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [h₃.other _ (by decide), h₂.gpr, h₁.gpr, h3]
  · rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, h4]
  · rw [h₃.gpr, h₂.other _ (by decide), h₁.gpr, h5]
  · rw [h₃.mem, h₂.mem, h₁.mem, h4]; rfl
  · rw [h₃.rd, h₂.rd, h₁.rd]
  · rw [h₃.wr, h₂.wr, h₁.wr]
  · rw [h₃.sp, h₂.sp, h₁.sp]
  · obtain ⟨-, n1, -, n3, -, -⟩ := pres_ne hr
    rw [h₃.other _ n3, h₂.other _ n1, h₁.gpr]

end

/-- After zeroing `k` coefficients of the polynomial at `P`. -/
structure ZeroInv (P : Addr) (s₀ : State) (k : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = P + BitVec.ofNat 64 (4 * k)
  a1 : s.gpr .a1 = 0
  a2 : s.gpr .a2 = BitVec.ofNat 64 (256 - k)
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion P] s₀.mem s.mem
  zero : ∀ t < 256, coeffAt s.mem P t = if t < k then 0 else coeffAt s₀.mem P t

theorem zero_step {P : Addr} {s₀ : State} (cw : Covers [polyRegion P] s₀.wr) (aP : P.toNat % 4 = 0) {k : Nat}
    (hk : k < 256) {s : State} (h : ZeroInv P s₀ k s) :
    WP isa (.block zeroBody) s fun s' => ZeroInv P s₀ (k + 1) s' ∧ (s'.gpr .a2 != 0) = decide (k + 1 ≠ 256) := by
  have cP : (polyRegion P).Contains (coeffAddr P k) 4 :=
    coeff_contains _ (by rw [VG.Proof.MlKem.n_eq]; exact hk)
  refine WP.mono (zeroBody_ok h.a0 h.a1 h.a2 (by rw [h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cP⟩)
    (align4_add aP _))
    fun s' ⟨r3, r4, r5, m, rd, wr, sp, cs⟩ => ⟨⟨?_, r4, ?_, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, ?_⟩, ?_⟩
  · rw [r3]; exact ptr_succ _ 4 k
  · rw [r5]; exact count_sub hk
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cP
  · rw [m]; exact coeff_one hk h.zero rfl
  · rw [r5, count_sub hk]; exact count_nz hk (by decide)

/-- Polynomial `j` of `scratch` is aligned. -/
theorem Ctx.alP {L : Lay} {s : State} (hc : Ctx L s) (j : Nat) : L.Al 0 (oPoly j) := by
  have := hc.al0
  have h8 : oPoly j % 8 = 0 := by unfold oPoly; omega
  show (L.ptr 0 + BitVec.ofNat 64 (oPoly j)).toNat % 8 = 0
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem zeroPoly_ok {L : Lay} {s : State} (hc : Ctx L s) {j : Nat} (hoff : oPoly j + 1024 ≤ 32768) :
    WP isa (zeroPoly j) s fun s' => Kept (L.RL [(0, oPoly j, 1024)]) s s' ∧ PolyIs s'.mem (L.A 0 (oPoly j)) zero := by
  have hfin : ∀ s', ZeroInv (L.A 0 (oPoly j)) s 256 s' →
      Kept (L.RL [(0, oPoly j, 1024)]) s s' ∧ PolyIs s'.mem (L.A 0 (oPoly j)) zero := fun s' h => by
    refine ⟨⟨h.cs, h.sp, h.rd, h.wr, h.frame⟩, ?_⟩
    refine polyIs_of_coeffAt fun t ht => ?_
    rw [h.zero t (by rw [VG.Proof.MlKem.n_eq] at ht; exact ht),
      ite_eq_left (by rw [VG.Proof.MlKem.n_eq] at ht; exact ht), zero,
      getElem!_pos (Vector.replicate n (0 : Zq)) t ht, Vector.getElem_replicate]
    rfl
  have hj : j + 2 < 2048 := by unfold oPoly at hoff; omega
  refine WP.seq (wp_polyAddr hj (by decide) fun s₁ h₁ => wp_li (by decide) fun s₂ h₂ =>
    wp_li (by decide) fun s₃ h₃ => WP.block_nil ?_)
  refine wp_loop_nz (ZeroInv (L.A 0 (oPoly j)) s) (N := 256) (by decide)
    (fun k hk s h => zero_step (hc.cs hoff) (hc.alP j).four hk h) hfin ?_
  refine ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, fun t _ => ?_⟩
  · rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, hc.s11]; simp
  · rw [h₃.other _ (by decide), h₂.gpr]; rfl
  · rw [h₃.gpr]
  · obtain ⟨-, n0, n1, n2, -, -⟩ := pres_ne hr
    rw [h₃.other _ n2, h₂.other _ n1, h₁.other _ n0]
  · rw [h₃.rd, h₂.rd, h₁.rd]
  · rw [h₃.wr, h₂.wr, h₁.wr]
  · rw [h₃.sp, h₂.sp, h₁.sp]
  · rw [h₃.mem, h₂.mem, h₁.mem]; exact Frame.refl _ _
  · rw [h₃.mem, h₂.mem, h₁.mem]; rfl

end VG.Proof.MlKem.RISCV64
