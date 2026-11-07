module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Store
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Transpose
import VerifiedGarbage.Proof.ChaCha20.Keystream
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.AddrArith

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4

/-- One 16-byte row of the final four ChaCha blocks. -/
def output (vs : Nat → CState) (n : Nat) : BitVec 128 :=
  ofVWords ((vs (n / 4))[4 * (n % 4)]'(by omega))
    ((vs (n / 4))[4 * (n % 4) + 1]'(by omega))
    ((vs (n / 4))[4 * (n % 4) + 2]'(by omega))
    ((vs (n / 4))[4 * (n % 4) + 3]'(by omega))

theorem output_slot (vs : Nat → CState) (r j : Fin 4) :
    output vs (slot r j) = ofVWords ((vs j)[rowWord r 0]) ((vs j)[rowWord r 1])
      ((vs j)[rowWord r 2]) ((vs j)[rowWord r 3]) := by
  have hd : slot r j / 4 = j.val := by unfold slot; omega
  have hm : slot r j % 4 = r.val := by unfold slot; omega
  simp only [output, hd, hm, rowWord, Fin.getElem_fin]; rfl

structure Keep (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.trans {s₀ s₁ s₂ : State} (h : Keep s₀ s₁) (h' : Keep s₁ s₂) : Keep s₀ s₂ :=
  ⟨h'.gpr.trans h.gpr, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

def rowSlots (r : Fin 4) : List Nat := (List.finRange 4).map (slot r)

/-- Row `r` of the four blocks transposed and XORed with the source (at `x1`,
`q`) into the destination (at `d`, `p`). -/
theorem finishRowForTo_ok (d : Reg) (js : List (Fin 4)) (hj : js.Nodup) {s : State} {m₀ : Mem}
    {q p : Addr} {N : Nat} {vs : Nat → CState} {done : List Nat}
    (r : Fin 4) (hd : DataTo m₀ s.mem q p N (output vs) done) (hq : s.gpr .x1 = q)
    (hp : s.gpr d = p) (halias : q = p ∨ (⟨q, N⟩ : Region).Disjoint ⟨p, N⟩) (hN : N ≤ 2 ^ 64)
    (hv : ∀ i j : Fin 4, vword (s.v (vreg (rowWord r i))) j = (vs j)[rowWord r i])
    (hfresh : ∀ j ∈ js, slot r j ∉ done)
    (hfit : ∀ j ∈ js, 16 * slot r j + 16 ≤ N)
    (hin : ∀ j ∈ js, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : ∀ j ∈ js, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (finishRowForTo d js r)) s fun s' =>
      DataTo m₀ s'.mem q p N (output vs) (js.map (slot r) ++ done) ∧
      (∀ k : Fin 16, k.val / 4 ≠ r.val → s'.v (vreg k) = s.v (vreg k)) ∧ Keep s s' := by
  apply WP.block_append
  refine (transpose_ok s r).mono fun t ⟨ht, ho, hs⟩ => ?_
  have hd' : DataTo m₀ t.mem q p N (output vs) done := hs.mem ▸ hd
  have hq' : t.gpr .x1 = q := by rw [hs.gpr, hq]
  have hp' : t.gpr d = p := by rw [hs.gpr, hp]
  have hv' : ∀ j : Fin 4, t.v (vreg (rowWord r j)) = output vs (slot r j) := by
    intro j; rw [ht j, transposed, output_slot, hv 0 j, hv 1 j, hv 2 j, hv 3 j]
  have hin' : ∀ j ∈ js, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro j hjs; rw [hs.rd, hs.wr]; exact hin j hjs
  have hout' : ∀ j ∈ js, InRegions t.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro j hjs; rw [hs.wr]; exact hout j hjs
  refine (xorListTo_ok d r js hj hd' hq' hp' halias hN hv'
    hfresh hfit hin' hout').mono fun u ⟨hu, hk⟩ => ⟨hu, ?_, ?_⟩
  · intro k hkr; rw [hk.v, ho k hkr]
  · exact ⟨hk.gpr.trans hs.gpr, hk.rd.trans hs.rd, hk.wr.trans hs.wr, hk.sp.trans hs.sp⟩

theorem slot_ne {r t : Fin 4} (hne : r ≠ t) (i j : Fin 4) : slot r i ≠ slot t j := by
  intro e; apply hne; apply Fin.ext; unfold slot at e; omega

theorem finishRowsForTo_ok (d : Reg) (js : List (Fin 4)) (hj : js.Nodup) (rs : List (Fin 4))
    (hn : rs.Nodup) {s : State} {m₀ : Mem} {q p : Addr} {N : Nat} {vs : Nat → CState}
    {done : List Nat}
    (hd : DataTo m₀ s.mem q p N (output vs) done) (hq : s.gpr .x1 = q) (hp : s.gpr d = p)
    (halias : q = p ∨ (⟨q, N⟩ : Region).Disjoint ⟨p, N⟩) (hN : N ≤ 2 ^ 64)
    (hv : ∀ r ∈ rs, ∀ i j : Fin 4, vword (s.v (vreg (rowWord r i))) j = (vs j)[rowWord r i])
    (hfresh : ∀ r ∈ rs, ∀ j ∈ js, slot r j ∉ done)
    (hfit : ∀ r : Fin 4, ∀ j ∈ js, 16 * slot r j + 16 ≤ N)
    (hin : ∀ r : Fin 4, ∀ j ∈ js, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : ∀ r : Fin 4, ∀ j ∈ js, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (rs.flatMap (finishRowForTo d js))) s fun s' =>
      DataTo m₀ s'.mem q p N (output vs) (rs.flatMap (fun r => js.map (slot r)) ++ done) ∧
        Keep s s' := by
  induction rs generalizing s done with
  | nil => exact WP.block_nil ⟨hd, rfl, rfl, rfl, rfl⟩
  | cons r rs ih =>
    have hr := (List.nodup_cons.mp hn).1
    apply WP.block_append
    refine (finishRowForTo_ok d js hj r hd hq hp halias hN (hv r (List.mem_cons_self ..))
      (hfresh r (List.mem_cons_self ..)) (hfit r) (hin r) (hout r)).mono fun t ⟨ht, hvkeep, hs⟩ => ?_
    have hq' : t.gpr .x1 = q := by rw [hs.gpr, hq]
    have hp' : t.gpr d = p := by rw [hs.gpr, hp]
    have hv' : ∀ x ∈ rs, ∀ i j : Fin 4,
        vword (t.v (vreg (rowWord x i))) j = (vs j)[rowWord x i] := by
      intro x hx i j
      have hxr : (rowWord x i).val / 4 ≠ r.val := by
        have hxr : x ≠ r := fun e => hr (e ▸ hx)
        simp only [rowWord] at *; omega
      rw [hvkeep _ hxr]; exact hv x (List.mem_cons_of_mem _ hx) i j
    have hfresh' : ∀ x ∈ rs, ∀ j ∈ js, slot x j ∉ js.map (slot r) ++ done := by
      intro x hx j hjs
      simp only [List.mem_append, not_or]
      refine ⟨?_, hfresh x (List.mem_cons_of_mem _ hx) j hjs⟩
      intro hm
      obtain ⟨i, _, he⟩ := List.mem_map.mp hm
      exact slot_ne (fun (e : x = r) => hr (e ▸ hx)) j i he.symm
    have hin' : ∀ x : Fin 4, ∀ j ∈ js,
        InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 (64 * j + 16 * x)) 16 := by
      intro x j hjs; rw [hs.rd, hs.wr]; exact hin x j hjs
    have hout' : ∀ x : Fin 4, ∀ j ∈ js, InRegions t.wr (p + BitVec.ofNat 64 (64 * j + 16 * x)) 16 := by
      intro x j hjs; rw [hs.wr]; exact hout x j hjs
    refine (ih (List.nodup_cons.mp hn).2 ht hq' hp' hv' hfresh' hin' hout').mono fun u ⟨hu, hk⟩ =>
      ⟨?_, hs.trans hk⟩
    intro x
    simpa only [DataTo, List.flatMap_cons, List.mem_append, or_assoc, or_left_comm] using hu x

theorem all_slots (n : Fin 16) : n.val ∈ (List.finRange 4).flatMap rowSlots :=
  (show ∀ n : Fin 16, n.val ∈ (List.finRange 4).flatMap rowSlots by decide) n

theorem output_word (vs : Nat → CState) (n : Nat) {e : Nat} (he : e < 4) :
    vword (output vs n) e = (vs (n / 4))[4 * (n % 4) + e]'(by omega) := by
  rw [output, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem byte_vword (v : BitVec 128) {i : Nat} (_hi : i < 16) :
    v.extractLsb' (8 * i) 8 = (vword v (i / 4)).extractLsb' (8 * (i % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    show 8 * (i % 4) + b < 32 by omega]
  exact congrArg v.getLsbD (by omega)

theorem output_byte (vs : Nat → CState) {k : Nat} (_hk : k < 256) :
    (output vs (k / 16)).extractLsb' (8 * (k % 16)) 8 =
      (VG.Spec.ChaCha20.serialize (vs (k / 64))).getD (k % 64) 0 := by
  rw [byte_vword _ (by omega), output_word _ _ (by omega),
    VG.Proof.ChaCha20.serialize_getD _ (by omega)]
  simp only [show k / 16 / 4 = k / 64 by omega,
    show 4 * (k / 16 % 4) + k % 16 / 4 = k % 64 / 4 by omega,
    show k % 16 % 4 = k % 64 % 4 by omega]

/-- The four blocks' keystream XORed with the 256 bytes of the source (at
`x1`) into the destination (at `d`), which is the source or apart from it. -/
theorem finishBlocksTo_ok (d : Reg) {s : State} {vs : Nat → CState} (h : Holds vs s)
    (halias : s.gpr .x1 = s.gpr d ∨ (⟨s.gpr .x1, 256⟩ : Region).Disjoint ⟨s.gpr d, 256⟩)
    (hin : ∀ r j : Fin 4, InRegions (s.rd ++ s.wr)
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : ∀ r j : Fin 4, InRegions s.wr
      (s.gpr d + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block ((List.finRange 4).flatMap (finishRowTo d))) s fun s' =>
      (∀ k < 256, s'.mem (s.gpr d + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (VG.Spec.ChaCha20.serialize (vs (k / 64))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr d, 256⟩] s.mem s'.mem ∧ Keep s s' := by
  refine (finishRowsForTo_ok d (List.finRange 4) (List.nodup_finRange 4) (List.finRange 4)
    (List.nodup_finRange 4) (DataTo.nil s.mem (s.gpr .x1) (s.gpr d) 256 (output vs)) rfl rfl halias
    (by decide) (fun r _ i j => h (rowWord r i) j j.isLt) (fun _ _ _ _ => List.not_mem_nil)
    (fun r j _ => by have := slot_lt r j; omega) (fun r j _ => hin r j)
    (fun r j _ => hout r j)).mono fun s' ⟨hd, hs⟩ => ⟨?_, hd.frame, hs⟩
  intro k hk
  rw [hd _, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    ite_eq_left ⟨List.mem_append_left _ (all_slots ⟨k / 16, by omega⟩), hk⟩,
    output_byte vs hk]

/-- `finishBlocksTo_ok` in place. -/
theorem finishBlocks_ok {s : State} {vs : Nat → CState} (h : Holds vs s)
    (hout : ∀ r j : Fin 4, InRegions s.wr
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block ((List.finRange 4).flatMap finishRow)) s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (VG.Spec.ChaCha20.serialize (vs (k / 64))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1, 256⟩] s.mem s'.mem ∧ Keep s s' :=
  finishBlocksTo_ok .x1 h (.inl rfl)
    (fun r j => by obtain ⟨q, hq, hc⟩ := hout r j; exact ⟨q, List.mem_append_right _ hq, hc⟩) hout

end VG.Proof.ChaCha20.AArch64.Neon4
