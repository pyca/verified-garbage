module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeLoop
import VerifiedGarbage.Proof.Framework.Block

/-!
# ML-KEM on AArch64: `ceLoop`

The constants (`wp_dupW`, `wp_bytesVec`), then the loop (`vloop_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `t` is `s` but for `x9` and the vector registers. -/
structure GFr (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem GFr.refl (s : State) : GFr s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem GFr.trans {s t u : State} (h : GFr s t) (h' : GFr t u) : GFr s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
   h'.sp.trans h.sp⟩

theorem GFr.of_only {s t : State} (h : Only [.x9] s t) : GFr s t :=
  ⟨fun r hr => h.gpr r (by simpa using hr), h.mem, h.rd, h.wr, h.sp⟩

theorem GFr.of_upd {s t : State} {d : VReg} {x : BitVec 128} (h : VUpd s t d x) : GFr s t :=
  ⟨fun r _ => by rw [h.gpr], h.mem, h.rd, h.wr, h.sp⟩

theorem movImm_noV (d : Reg) (v : BitVec 64) : ((movImm d v).all fun i => !writesV i) = true := by
  simp [movImm, writesV]

/-- `movImm x9 c` and what follows it. -/
theorem wp_movImm9 {s : State} {c : BitVec 64} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, GFr s t → t.v = s.v → t.gpr .x9 = c → WP isa (.block is) t Q) :
    WP isa (.block (movImm .x9 c ++ is)) s Q :=
  wp_scalar (movImm_noV _ _) (wp_movImm (is := []) fun _ h e => wp_nil (Q := fun t => Only [.x9] s t ∧ t.gpr .x9 = c)
    ⟨h, e⟩) fun t ⟨h, e⟩ v => k t (.of_only h) v e

/-- `c` in every word of `v`. -/
theorem wp_dupW {s : State} {v : VReg} {c : Nat} (hc : c < 2 ^ 32) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, GFr s t → (∀ r, r ≠ v → t.v r = s.v r) → Lanes (t.v v) (fun _ => c) → WP isa (.block is) t Q) :
    WP isa (.block (dupW v c ++ is)) s Q := by
  unfold dupW
  rw [List.append_assoc]
  refine wp_movImm9 fun s1 g1 v1 e1 => wp_vop rfl fun s2 h2 => k s2 (g1.trans (.of_upd h2))
    (fun r hr => by rw [h2.get r hr, v1]) ?_
  rw [h2.v]
  refine (lanes_dup).congr fun _ _ => ?_
  rw [e1, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide), Nat.mod_eq_of_lt hc]

/-- The bytes `xs` in `v`. -/
theorem wp_bytesVec {s : State} {v : VReg} {xs : List Nat} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, GFr s t → (∀ r, r ≠ v → t.v r = s.v r) →
      t.v v = setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (xs.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
        (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (xs.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
        (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (xs.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) →
      WP isa (.block is) t Q) :
    WP isa (.block (bytesVec v xs ++ is)) s Q := by
  unfold bytesVec
  simp only [List.append_assoc]
  refine wp_movImm9 fun s1 g1 v1 e1 => wp_vop rfl fun s2 h2 => ?_
  rw [List.singleton_append]
  refine wp_movImm9 fun s3 g3 v3 e3 => wp_vop rfl fun s4 h4 => k s4 (((g1.trans (.of_upd h2)).trans g3).trans
    (.of_upd h4)) (fun r hr => by rw [h4.get r hr, v3, h2.get r hr, v1]) ?_
  rw [h4.v, v3, h2.v, e1, e3]

/-- The loop of one width. -/
theorem vloop_ok {w : Width} (hw : WOk w) {G n : Nat} {K : State → Prop} {setup body : List Instr}
    {s₀ : State} (hn : 256 / (w.c * G) = n) (hn0 : 0 < n) (hG : w.nb * G * n = 32 * w.d)
    (hmul : w.mul < 2 ^ 32) (hmask : 2 ^ w.d - 1 < 2 ^ 32)
    (hset : ∀ s, WP isa (.block setup) s fun t => GFr s t ∧
      (∀ r, r ≠ .v20 → r ≠ .v21 → r ≠ .v22 → t.v r = s.v r) ∧ K t)
    (hK : ∀ s t, t.v = s.v → K s → K t)
    (hstep : ∀ k < n, ∀ s, VInv w G K s₀ k s →
      WP isa (.block body) s fun t => VInv w G K s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ n)) :
    WP isa (ceLoop w n setup body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      bytesAt s'.mem (oP s₀) (32 * w.d) = Spec.MlKem.compressEncode w.d (P s₀) := by
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine wp_dupW hmul fun s1 g1 v1 l16 => wp_dupW (c := w.add) (by have := hw.add_lt; omega) fun s2 g2 v2 l17 =>
    wp_dupW hmask fun s3 g3 v3 l18 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hset s3) fun s4 ⟨g4, v4, k4⟩ => ?_
  rw [← List.append_nil (movImm .x11 _)]
  refine wp_scalar (movImm_noV _ _) (wp_movImm (is := []) fun t h e =>
    wp_nil (Q := fun t => Only [.x11] s4 t ∧ t.gpr .x11 = BitVec.ofNat 64 n) ⟨h, e⟩) fun s5 ⟨h5, e5⟩ v5 => wp_nil ?_
  have g : ∀ r, r ≠ .x9 → r ≠ .x11 → s5.gpr r = s₀.gpr r := fun r h9 h11 => by
    rw [h5.gpr r (by simpa using h11), g4.gpr r h9, g3.gpr r h9, g2.gpr r h9, g1.gpr r h9]
  have m5 : s5.mem = s₀.mem := by rw [h5.mem, g4.mem, g3.mem, g2.mem, g1.mem]
  have vv : ∀ r, r ≠ .v20 → r ≠ .v21 → r ≠ .v22 → s5.v r = s3.v r := fun r a b c => by rw [v5, v4 r a b c]
  have h0 : VInv w G K s₀ 0 s5 := by
    refine ⟨by rw [h5.rd, g4.rd, g3.rd, g2.rd, g1.rd], by rw [h5.wr, g4.wr, g3.wr, g2.wr, g1.wr],
      by rw [h5.sp, g4.sp, g3.sp, g2.sp, g1.sp], ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, hK _ _ v5 k4, ?_, ?_⟩
    · rw [g .x0 (by decide) (by decide), Nat.mul_zero]; exact (ptr_zero _).symm
    · rw [g .x2 (by decide) (by decide), Nat.mul_zero, ptr_zero]
    · rw [e5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.div_le_self 256 (w.c * G); omega), hn,
        Nat.sub_zero]
    · rw [vv _ (by decide) (by decide) (by decide), v3 _ (by decide), v2 _ (by decide)]
      exact l16
    · rw [vv _ (by decide) (by decide) (by decide), v3 _ (by decide)]; exact l17
    · rw [vv _ (by decide) (by decide) (by decide)]; exact l18
    · rw [m5, Nat.mul_zero]; exact BytesUpTo.zero _
    · rw [m5]; exact Frame.refl _ _
  refine WP.mono (count_loop hn0 (VInv w G K s₀) hstep h0) fun s' h => ⟨h.rd, h.wr, h.sp, ?_⟩
  rw [← hn] at h
  exact h.done (by rw [hn]; exact hG)

end VG.Proof.MlKem.AArch64.CE
