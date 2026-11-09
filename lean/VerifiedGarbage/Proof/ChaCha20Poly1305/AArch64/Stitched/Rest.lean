module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Last
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.LoopRounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rotate
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.RoundLoop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Transpose
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.CachedAdd
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Poly1305.AArch64.Init
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Setup
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the rest of the data

`vg_chacha20_xor` (any backend) on the data after the first `P` bytes (the
chunks, and when encrypting with SVE2 up to 256 bytes more), from the counter
after them: the whole data encrypted from counter 1.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_mov)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

/-- The data after its first `P` bytes. -/
abbrev restR (s₀ : State) (P : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 P, L s₀ - P⟩

theorem data_in {s₀ : State} {k : Nat} (hk : k < L s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base _ (by omega) (by have h : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt; omega)

theorem not_rest {s₀ : State} {P k : Nat} (hk : k < P) (hP : P ≤ L s₀) :
    ¬ (restR s₀ P).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

/-- The keystream from block `q`. -/
theorem ks_shift (S : VG.Proof.ChaCha20.CState) {len q k : Nat} (hk : k < len) (hq : 64 * q ≤ k) :
    (keystream S len).getD k 0 =
      (Spec.ChaCha20.serialize (Spec.ChaCha20.block (ctr (ctr S q) ((k - 64 * q) / 64)))).getD
        ((k - 64 * q) % 64) 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ hk, VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
    show q + (k - 64 * q) / 64 = k / 64 by omega, show (k - 64 * q) % 64 = k % 64 by omega]

/-- The output after its first `P` bytes. -/
abbrev restQ (s₀ : State) (Q : Addr) (P : Nat) : Region :=
  ⟨Q + BitVec.ofNat 64 P, L s₀ - P⟩

theorem not_restQ {s₀ : State} {Q : Addr} {P k : Nat} (hk : k < P) (hP : P ≤ L s₀) :
    ¬ (restQ s₀ Q P).Contains (Q + BitVec.ofNat 64 k) 1 := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

/-- `bytesAt` of a destination XORed from a source. -/
theorem bytesAt_xor2 {m m' : Mem} {p q : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : ∀ k < n, m' (q + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0) :
    Spec.ChaCha20.bytesAt m' q n = List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt m p n) ks := by
  apply List.ext_getElem
  · simp [Spec.ChaCha20.bytesAt, hks]
  · intro k h₁ h₂
    simp only [Spec.ChaCha20.bytesAt, List.length_map, List.length_range] at h₁
    simp only [Spec.ChaCha20.bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
    rw [h k h₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega_arith), Option.getD_some]

/-- The data from `P`, encrypted from the counter after `P / 64` blocks (if
any data follows), into the output (`XorCallee.callWith (!e)`), whose first
`P` bytes are the data's encrypted. -/
theorem rest_callOut (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀) {s w : State}
    {P : Nat} (hle : P ≤ L s₀) (hP : P < L s₀ → P % 64 = 0)
    (hx0 : w.gpr .x0 = off (cx s₀) 64) (hx1 : w.gpr .x1 = dp s₀ + BitVec.ofNat 64 P)
    (hx2 : w.gpr .x2 = BitVec.ofNat 64 (L s₀ - P)) (hx3 : w.gpr .x3 = off (cx s₀) 128)
    (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr) (h28 : w.gpr .x28 = s₀.gpr .x28)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hdata : ∀ k < L s₀, P ≤ k → w.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k))
    (hout : ∀ k < P, w.mem (op e s₀ + BitVec.ofNat 64 k) =
      s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0) :
    WP isa (v.callee.callWith (!e)) w fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, oR e s₀] w s' ∧ Frame [sub s₀ 64 384, restQ s₀ (op e s₀) P] w.mem s'.mem ∧
      bytesAt s'.mem (op e s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have wo := hp.o.wrap
  have ts : Region.Sub (restQ s₀ (op e s₀) P) (oR e s₀) := Offset.sub_base _ (by omega)
  refine xor_callOut v hp hrd hwr h28 hx0 hx1 hx2 hx3 (by omega) fun s' v' k' d' => ?_
  refine ⟨v', ?_, ?_, ?_⟩
  · refine k'.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨oR e s₀, by simp, ts⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · refine k'.frame.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨restQ s₀ (op e s₀) P, by simp, fun _ h => h⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · show Spec.ChaCha20.bytesAt _ _ _ = Spec.ChaCha20.encrypt _ _ _ (Spec.ChaCha20.bytesAt _ _ _)
    rw [encrypt_eq, show (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ from
      VG.Proof.Poly1305.length_bytesAt _ _ _]
    refine bytesAt_xor2 (VG.Proof.ChaCha20.length_keystream _ _) fun k hk => ?_
    by_cases hk' : k < P
    · have hin : (oR e s₀).Contains (op e s₀ + BitVec.ofNat 64 k) 1 :=
        Offset.contains_base _ (by omega) (by omega)
      have hs : ¬ (⟨off (cx s₀) 64, 64⟩ : Region).Contains (op e s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.o.ctx.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)) _ hh hin
      have hb : ¬ (⟨off (cx s₀) 128, 320⟩ : Region).Contains (op e s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.o.ctx.sub_left (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega)) _ hh hin
      rw [k'.frame _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hs
        · exact not_restQ hk' hle
        · exact hb), hout k hk']
    · have hPL : P < L s₀ := by omega
      have h64 := hP hPL
      have ea : ∀ X : Addr, X + BitVec.ofNat 64 P + BitVec.ofNat 64 (k - P) = X + BitVec.ofNat 64 k := fun X => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
      have x := VG.Proof.ChaCha20.AArch64.Xor.bytes_of_to
        (VG.Proof.ChaCha20.length_keystream _ _) d' (k := k - P) (by omega)
      rw [ea, ea, hdata k hk (by omega), hcnt hPL, VG.Proof.ChaCha20.keystream_getD _ (by omega)] at x
      rw [x, ks_shift _ hk (q := P / 64) (by omega), show 64 * (P / 64) = P by omega]

/-- `rest_callOut` in place (`seal`), from the data's first `P` bytes
encrypted in place. -/
theorem rest_call (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) {s w : State}
    {P : Nat} (hle : P ≤ L s₀) (hP : P < L s₀ → P % 64 = 0)
    (hx0 : w.gpr .x0 = off (cx s₀) 64) (hx1 : w.gpr .x1 = dp s₀ + BitVec.ofNat 64 P)
    (hx2 : w.gpr .x2 = BitVec.ofNat 64 (L s₀ - P)) (hx3 : w.gpr .x3 = off (cx s₀) 128)
    (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr) (h28 : w.gpr .x28 = s₀.gpr .x28)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hdata : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < P then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k)) :
    WP isa v.callee.inPlace w fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, dR s₀] w s' ∧ Frame [sub s₀ 64 384, restR s₀ P] w.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) :=
  rest_callOut v hp hle hP hx0 hx1 hx2 hx3 hrd hwr h28 hcnt
    (fun k hk hkp => by rw [hdata k hk, ite_eq_right (by omega)])
    (fun k hk => by rw [op_true, hdata k (by omega), ite_eq_left hk])

/-- The data before the rest is kept. -/
theorem prefix_rest {s₀ : State} (hp : APre e s₀) {m m' : Mem} {P n : Nat}
    (hf : Frame [sub s₀ 64 384, restR s₀ P] m m') (hn : n ≤ P) (hP : P ≤ L s₀) :
    bytesAt m' (dp s₀) n = bytesAt m (dp s₀) n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact fun hh => hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 384) (by lit_omega)) _ hh
      (data_in (by omega))
  · exact not_rest (by omega) hP

/-- `cryptRest`'s arguments: the stream's, from the context and `x22`, `x23`. -/
theorem restArgs_ok {s₀ : State} {w : State} (hx21 : w.gpr .x21 = cx s₀) :
    WP isa (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23, .addImm .x .x3 .x21 128]) w
      fun w' => (w'.gpr .x0 = off (cx s₀) 64 ∧ w'.gpr .x1 = w.gpr .x22 ∧ w'.gpr .x2 = w.gpr .x23 ∧
        w'.gpr .x3 = off (cx s₀) 128 ∧ Kept [] w w') ∧
        ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  have core : WP isa (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23,
      .addImm .x .x3 .x21 128]) w fun w' =>
      w'.gpr .x0 = off (cx s₀) 64 ∧ w'.gpr .x1 = w.gpr .x22 ∧ w'.gpr .x2 = w.gpr .x23 ∧
      w'.gpr .x3 = off (cx s₀) 128 ∧ w'.mem = w.mem ∧ w'.rd = w.rd ∧ w'.wr = w.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ =>
      wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
        ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hx21],
          by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)],
          by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
          by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21],
          by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
          by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  refine WP.preservedV (WP.mono (WP.kept core (by rfl))
    fun w' ⟨⟨h0, h1, h2, h3, hm, hrd, hwr⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, h3, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩) (by lit_decide)

end VG.Proof.ChaCha20Poly1305.AArch64
