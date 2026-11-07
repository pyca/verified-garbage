module
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4

structure StoreSame (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  v : ∀ k : Fin 16, s'.v (vreg k) = s.v (vreg k)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem StoreSame.trans {s₀ s₁ s₂ : State} (h : StoreSame s₀ s₁) (h' : StoreSame s₁ s₂) :
    StoreSame s₀ s₂ := ⟨h'.gpr.trans h.gpr, fun k => (h'.v k).trans (h.v k),
      h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

/-- Row `r` of block `j`: the source's (at `x1`) XORed with the keystream's
into the destination (at `d`). -/
theorem xorRowTo_ok (s : State) (d : Reg) (r j : Fin 4)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : InRegions s.wr (s.gpr d + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (xorRowTo d r j)) s fun s' =>
      s'.mem = s.mem.write (s.gpr d + BitVec.ofNat 64 (64 * j + 16 * r)) 16
        (s.mem.read (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 ^^^
          s.v (vreg (rowWord r j))) ∧ StoreSame s s' := by
  have ha : (64 * j.val + 16 * r.val) % 16 = 0 ∧ 64 * j.val + 16 * r.val < 4096 * 16 := by omega
  apply WP.of_runBlock
  simp only [xorRowTo, runBlock_cons, runBlock_nil, exec, addr, ha, and_self, ite_true, State.load, hin,
    Option.bind_some, Option.map_some, isa, runStep_some, RegUpd.gpr_setV, RegUpd.v_setV,
    vreg_ne, ite_false, VOp.eval, State.store,
    RegUpd.wr_setV, hout, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro k; simp only [RegUpd.v_setV, vreg_ne, ite_false]

theorem xorRow_ok (s : State) (r j : Fin 4)
    (hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (xorRow r j)) s fun s' =>
      s'.mem = s.mem.write (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16
        (s.mem.read (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 ^^^
          s.v (vreg (rowWord r j))) ∧ StoreSame s s' :=
  xorRowTo_ok s .x1 r j (by obtain ⟨q, hq, hc⟩ := hout; exact ⟨q, List.mem_append_right _ hq, hc⟩) hout

/-- A byte of a 16-byte vector load. -/
theorem byte_read16 (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (m.read p 16).extractLsb' (8 * i) 8 = m (p + BitVec.ofNat 64 i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
  rw [getLsbD_read m 16 p _ (by omega), show (8 * i + b) / 8 = i by omega,
    show (8 * i + b) % 8 = b by omega]

theorem xor_write_byte (m : Mem) (p : Addr) (v : BitVec 128) {i : Nat} (hi : i < 16) :
    (m.write p 16 (m.read p 16 ^^^ v)) (p + BitVec.ofNat 64 i) =
      m (p + BitVec.ofNat 64 i) ^^^ v.extractLsb' (8 * i) 8 := by
  simp only [Mem.write, Mem.sub_ofNat_toNat p (by omega : i < 2 ^ 64), hi, ite_true,
    BitVec.extractLsb'_xor, byte_read16 m p hi]

theorem xor_write_apply (m : Mem) (p : Addr) (v : BitVec 128) (x : Addr) :
    (m.write p 16 (m.read p 16 ^^^ v)) x =
      if (x - p).toNat < 16 then m x ^^^ v.extractLsb' (8 * (x - p).toNat) 8 else m x := by
  by_cases h : (x - p).toNat < 16
  · simp only [Mem.write, h, ite_true, BitVec.extractLsb'_xor, byte_read16 m p h]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm p (x - p), BitVec.sub_add_cancel]
  · rw [ite_eq_right h]; exact Mem.write_apply h

/-- A sequence of distinct, aligned vector stores, tracked by their 16-byte slot. -/
def Data (m₀ m : Mem) (p : Addr) (out : Nat → BitVec 128) (done : List Nat) : Prop :=
  ∀ x, m x = if (x - p).toNat / 16 ∈ done ∧ (x - p).toNat < 256
    then m₀ x ^^^ (out ((x - p).toNat / 16)).extractLsb' (8 * ((x - p).toNat % 16)) 8
    else m₀ x

theorem Data.nil (m : Mem) (p : Addr) (out : Nat → BitVec 128) : Data m m p out [] := by
  intro x; simp only [List.not_mem_nil, false_and, ite_false]

theorem Data.store {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : Data m₀ m p out done) {n : Nat} (hn : n < 16) (hfresh : n ∉ done) :
    Data m₀ (m.write (p + BitVec.ofNat 64 (16 * n)) 16
      (m.read (p + BitVec.ofNat 64 (16 * n)) 16 ^^^ out n)) p out (n :: done) := by
  intro x
  rw [xor_write_apply]
  simp only [Offset.lt_iff x p (by omega : 16 * n + 16 ≤ 2 ^ 64)]
  rw [h x]
  have hx := (x - p).isLt
  by_cases he : (x - p).toNat / 16 = n ∧ (x - p).toNat < 256
  · obtain ⟨he, hb⟩ := he
    have hd : 16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16 := by omega
    have hs : (x - (p + BitVec.ofNat 64 (16 * n))).toNat = (x - p).toNat % 16 := by
      rw [Offset.toNat_sub_add x p (by omega)]
      have hh : 2 ^ 64 - 16 * n + (x - p).toNat = 2 ^ 64 + (x - p).toNat % 16 := by omega
      rw [hh, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    simp only [hd, and_self, ite_true, he, hfresh, false_and, ite_false, hs,
      List.mem_cons_self, hb]
  · have hd : ¬(16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16) := by omega
    rw [ite_eq_right hd]
    by_cases hb : (x - p).toNat < 256
    · have hn' : (x - p).toNat / 16 ≠ n := by omega
      simp only [List.mem_cons, hn', false_or]
    · simp only [hb, and_false, ite_false]

/-- A 16-byte store of `w ^^^ v` at `p`, a byte at a time. -/
theorem xor_write_apply' (m : Mem) (p : Addr) (w v : BitVec 128) (x : Addr) :
    (m.write p 16 (w ^^^ v)) x =
      if (x - p).toNat < 16 then
        w.extractLsb' (8 * (x - p).toNat) 8 ^^^ v.extractLsb' (8 * (x - p).toNat) 8
      else m x := by
  by_cases h : (x - p).toNat < 16
  · simp only [Mem.write, h, ite_true, BitVec.extractLsb'_xor]
  · rw [ite_eq_right h]; exact Mem.write_apply h

/-- `Data` from a source: distinct, aligned 16-byte stores to the first `N`
bytes at `p` of the bytes of `m₀` at `q` XORed with `out`, tracked by their
slot. -/
def DataTo (m₀ m : Mem) (q p : Addr) (N : Nat) (out : Nat → BitVec 128) (done : List Nat) : Prop :=
  ∀ x, m x = if (x - p).toNat / 16 ∈ done ∧ (x - p).toNat < N
    then m₀ (q + (x - p)) ^^^ (out ((x - p).toNat / 16)).extractLsb' (8 * ((x - p).toNat % 16)) 8
    else m₀ x

theorem DataTo.nil (m : Mem) (q p : Addr) (N : Nat) (out : Nat → BitVec 128) :
    DataTo m m q p N out [] := by
  intro x; simp only [List.not_mem_nil, false_and, ite_false]

theorem DataTo.frame {m₀ m : Mem} {q p : Addr} {N : Nat} {out : Nat → BitVec 128} {done : List Nat}
    (h : DataTo m₀ m q p N out done) : Frame [⟨p, N⟩] m₀ m := by
  intro x hx
  have hn : ¬ (x - p).toNat < N := by
    have hh := hx ⟨p, N⟩ (List.mem_cons_self ..)
    simp only [Region.Contains] at hh
    omega
  rw [h x, ite_eq_right (fun h => hn h.2)]

/-- Slot `n` of the source is as in `m₀`, if it is not written yet: in
place, or apart from the destination. -/
theorem DataTo.src {m₀ m : Mem} {q p : Addr} {N : Nat} {out : Nat → BitVec 128} {done : List Nat}
    (h : DataTo m₀ m q p N out done) (halias : q = p ∨ (⟨q, N⟩ : Region).Disjoint ⟨p, N⟩)
    {n : Nat} (hn : 16 * n + 16 ≤ N) (hN : N ≤ 2 ^ 64) (hfresh : n ∉ done) :
    m.read (q + BitVec.ofNat 64 (16 * n)) 16 = m₀.read (q + BitVec.ofNat 64 (16 * n)) 16 := by
  refine Mem.read_congr fun i hi => ?_
  rw [Offset.add_add, h]
  refine ite_eq_right fun ⟨hs, hlt⟩ => ?_
  rcases halias with rfl | hd
  · rw [Mem.sub_ofNat_toNat _ (by omega)] at hs
    exact hfresh (by rwa [show (16 * n + i) / 16 = n by omega] at hs)
  · have hx : (⟨q, N⟩ : Region).Contains (q + BitVec.ofNat 64 (16 * n + i)) 1 := by
      show (q + BitVec.ofNat 64 (16 * n + i) - q).toNat + 1 ≤ N
      rw [Mem.sub_ofNat_toNat _ (by omega)]; omega
    exact hd _ hx (show (q + BitVec.ofNat 64 (16 * n + i) - p).toNat + 1 ≤ N by omega)

theorem DataTo.store {m₀ m : Mem} {q p : Addr} {N : Nat} {out : Nat → BitVec 128} {done : List Nat}
    (h : DataTo m₀ m q p N out done) {n : Nat} (hn : 16 * n + 16 ≤ N) (hN : N ≤ 2 ^ 64)
    (hsrc : m.read (q + BitVec.ofNat 64 (16 * n)) 16 = m₀.read (q + BitVec.ofNat 64 (16 * n)) 16) :
    DataTo m₀ (m.write (p + BitVec.ofNat 64 (16 * n)) 16
      (m.read (q + BitVec.ofNat 64 (16 * n)) 16 ^^^ out n)) q p N out (n :: done) := by
  intro x
  rw [xor_write_apply']
  simp only [Offset.lt_iff x p (by omega : 16 * n + 16 ≤ 2 ^ 64)]
  have hx := (x - p).isLt
  by_cases he : (x - p).toNat / 16 = n ∧ (x - p).toNat < N
  · obtain ⟨he, hb⟩ := he
    have hd : 16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16 := by omega
    have hs : (x - (p + BitVec.ofNat 64 (16 * n))).toNat = (x - p).toNat % 16 := by
      rw [Offset.toNat_sub_add x p (by omega)]
      have hh : 2 ^ 64 - 16 * n + (x - p).toNat = 2 ^ 64 + (x - p).toNat % 16 := by omega
      rw [hh, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hq : q + BitVec.ofNat 64 (16 * n) + BitVec.ofNat 64 ((x - p).toNat % 16) = q + (x - p) := by
      rw [Offset.add_add, show 16 * n + (x - p).toNat % 16 = (x - p).toNat by omega,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [hd, and_self, ite_true, he, hb, List.mem_cons_self, hs, hsrc,
      byte_read16 _ _ (Nat.mod_lt _ (by decide) : (x - p).toNat % 16 < 16), hq]
  · have hd : ¬(16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16) := by omega
    rw [ite_eq_right hd, h x]
    by_cases hb : (x - p).toNat < N
    · have hn' : (x - p).toNat / 16 ≠ n := by omega
      simp only [List.mem_cons, hn', false_or]
    · simp only [hb, and_false, ite_false]

def slot (r j : Fin 4) : Nat := 4 * j.val + r.val

theorem slot_lt (r j : Fin 4) : slot r j < 16 := by unfold slot; omega

theorem slot_inj (r i j : Fin 4) : slot r i = slot r j ↔ i = j := by
  simp only [slot, Fin.ext_iff]; omega

/-- Rows `r` of the blocks `js`, from the source at `x1` (`q`) to the destination
at `d` (`p`), which is the source or apart from it in their first `N` bytes. -/
theorem xorListTo_ok (d : Reg) (r : Fin 4) (js : List (Fin 4)) (hn : js.Nodup)
    {m₀ : Mem} {q p : Addr} {N : Nat} {out : Nat → BitVec 128} {done : List Nat} {s : State}
    (hd : DataTo m₀ s.mem q p N out done) (hq : s.gpr .x1 = q) (hp : s.gpr d = p)
    (halias : q = p ∨ (⟨q, N⟩ : Region).Disjoint ⟨p, N⟩) (hN : N ≤ 2 ^ 64)
    (hv : ∀ j : Fin 4, s.v (vreg (rowWord r j)) = out (slot r j))
    (hfresh : ∀ j ∈ js, slot r j ∉ done)
    (hfit : ∀ j ∈ js, 16 * slot r j + 16 ≤ N)
    (hin : ∀ j ∈ js, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : ∀ j ∈ js, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (js.flatMap (xorRowTo d r))) s fun s' =>
      DataTo m₀ s'.mem q p N out (js.map (slot r) ++ done) ∧ StoreSame s s' := by
  induction js generalizing s done with
  | nil => exact WP.block_nil ⟨hd, rfl, fun _ => rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    have hi : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
      rw [hq]; exact hin j (List.mem_cons_self ..)
    have ho : InRegions s.wr (s.gpr d + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
      rw [hp]; exact hout j (List.mem_cons_self ..)
    have he : 64 * j.val + 16 * r.val = 16 * slot r j := by unfold slot; omega
    apply WP.block_append
    refine (xorRowTo_ok s d r j hi ho).mono fun s' ⟨hm, hs⟩ => ?_
    have hd' : DataTo m₀ s'.mem q p N out (slot r j :: done) := by
      rw [hm, hp, hq, hv j, he]
      exact hd.store (hfit j (List.mem_cons_self ..)) hN
        (hd.src halias (hfit j (List.mem_cons_self ..)) hN (hfresh j (List.mem_cons_self ..)))
    have hq' : s'.gpr .x1 = q := by rw [hs.gpr, hq]
    have hp' : s'.gpr d = p := by rw [hs.gpr, hp]
    have hv' : ∀ i : Fin 4, s'.v (vreg (rowWord r i)) = out (slot r i) := by
      intro i; rw [hs.v, hv]
    have hfresh' : ∀ i ∈ js, slot r i ∉ slot r j :: done := by
      intro i hi
      simp only [List.mem_cons, slot_inj, not_or]
      exact ⟨fun e => (List.nodup_cons.mp hn).1 (e ▸ hi),
        hfresh i (List.mem_cons_of_mem _ hi)⟩
    have hin' : ∀ i ∈ js, InRegions (s'.rd ++ s'.wr) (q + BitVec.ofNat 64 (64 * i + 16 * r)) 16 := by
      intro i hi; rw [hs.rd, hs.wr]; exact hin i (List.mem_cons_of_mem _ hi)
    have hout' : ∀ i ∈ js, InRegions s'.wr (p + BitVec.ofNat 64 (64 * i + 16 * r)) 16 := by
      intro i hi; rw [hs.wr]; exact hout i (List.mem_cons_of_mem _ hi)
    refine (ih (List.nodup_cons.mp hn).2 hd' hq' hp' hv' hfresh'
      (fun i hi => hfit i (List.mem_cons_of_mem _ hi)) hin' hout').mono fun s'' ⟨hd'', ht⟩ =>
      ⟨?_, hs.trans ht⟩
    intro x
    simpa only [DataTo, List.map_cons, List.mem_append, List.mem_cons, or_assoc,
      or_left_comm] using hd'' x

end VG.Proof.ChaCha20.AArch64.Neon4
