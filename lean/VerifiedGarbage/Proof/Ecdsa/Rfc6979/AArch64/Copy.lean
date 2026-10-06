import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Regs
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on AArch64: copying words

`copyN k src so dst d` copies the `8 k` bytes at `src + so` to `dst + d`, a
word at a time through `x11`, when the two ranges are apart: each word
written is the word read (`copyW_ok`), so the bytes written are the bytes
read (`copyN_ok`, by induction on the words).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

/-- One word copied through `x11`. -/
theorem copyW_ok {u : State} {src dst : Reg} {S D : Addr} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    {so d : Nat} (hso : so % 8 = 0 ∧ so < 32768) (hdo : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 so) 8)
    (hw : InRegions u.wr (D + BitVec.ofNat 64 d) 8) (hdr : dst ≠ .x11) :
    WP isa (.block [.ldr .x .x11 src so, .str .x .x11 dst d]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.writeW (D + BitVec.ofNat 64 d) (u.mem.readW (S + BitVec.ofNat 64 so) 64) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, hso, hdo, and_self,
    ite_true, Option.bind_some, State.load, State.store, State.read, Size.bits, hs, hr, Option.map_some,
    RegUpd.gpr_write_of_ne _ _ _ hdr, hd, RegUpd.wr_write, hw, RegUpd.gpr_write_self, BitVec.setWidth_eq,
    read8, write8, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial, rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl⟩

theorem bytesAt_copied (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 64)) D 8 = Spec.Sha256.bytesAt m S 8 := by
  rw [show (64 : Nat) = 8 * 8 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 8) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem copyN_ok {src dst : Reg} {S D : Addr} {so d K : Nat} (hdr : dst ≠ .x11) (hsr : src ≠ .x11)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 8 * K⟩ ⟨D + BitVec.ofNat 64 d, 8 * K⟩)
    (hdn : d + 8 * K < 2 ^ 64) (hso : so % 8 = 0 ∧ so + 8 * K ≤ 32768) (hdo : d % 8 = 0 ∧ d + 8 * K ≤ 32768) :
    ∀ k ≤ K, ∀ u : State, u.gpr src = S → u.gpr dst = D →
      (∀ j < K, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + 8 * j)) 8) →
      (∀ j < K, InRegions u.wr (D + BitVec.ofNat 64 (d + 8 * j)) 8) →
      WP isa (.block (Cfg.copyN k src so dst d)) u fun u' =>
        u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧
        Frame [⟨D + BitVec.ofNat 64 d, 8 * K⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (D + BitVec.ofNat 64 d) (8 * k) =
          Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) (8 * k)
  | 0, _, u, _, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hs, hd, hr, hw => by
    rw [Cfg.copyN, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyN_ok hdr hsr hsep hdn hso hdo k (by omega) u hs hd hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (copyW_ok (u := u₁) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (hrd₁ ▸ hwr₁ ▸ hr k (by omega)) (hwr₁ ▸ hw k (by omega)) hdr)
      fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ?_
    -- The word written, within the destination.
    have hsub : Region.Sub ⟨D + BitVec.ofNat 64 (d + 8 * k), 8⟩ ⟨D + BitVec.ofNat 64 d, 8 * K⟩ :=
      Offset.sub _ (by omega) (by omega)
    have hf₂ : Frame [⟨D + BitVec.ofNat 64 (d + 8 * k), 8⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (Nat.le_refl _) (by omega) (by omega))
    -- The word read, unchanged by the earlier words.
    have hsrc : Spec.Sha256.bytesAt u₁.mem (S + BitVec.ofNat 64 (so + 8 * k)) 8 =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 (so + 8 * k)) 8 :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep.sub_left (Offset.sub _ (by omega) (by omega))) (by omega)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩), ?_⟩
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, Offset.add_add, ← hsrc]
    congr 1
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    · rw [hm₂]; exact bytesAt_copied _ _ _

/-- The first `n` of `k` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : n ≤ k) :
    Spec.Sha256.bytesAt m p n = (Spec.Sha256.bytesAt m p k).take n := by
  rw [show k = n + (k - n) by omega, Proof.Hmac.Common.bytesAt_add, List.take_left']
  simp [Spec.Sha256.bytesAt]

/-- `d ← src + k`. -/
theorem addImmX_ok {u : State} {d src : Reg} {S : Addr} (hs : u.gpr src = S) {k : Nat} (hk : k < 4096) :
    WP isa (.block [.addImm .x d src k]) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.mem = u.mem ∧ u'.gpr d = S + BitVec.ofNat 64 k ∧ ∀ r, r ≠ d → u'.gpr r = u.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hk, ite_true, State.read, Size.bits,
    BitVec.setWidth_eq, hs, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- The word at `src + k` copied to `dst + k`, through `x13`, `x14` and `x11`. -/
theorem copyAt_ok {u : State} {src dst : Reg} {S D : Addr} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    (hd13 : dst ≠ .x13) {k : Nat} (hk : k < 4096)
    (hr : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 k) 8) (hw : InRegions u.wr (D + BitVec.ofNat 64 k) 8) :
    WP isa (.block [.addImm .x .x13 src k, .addImm .x .x14 dst k, .ldr .x .x11 .x13 0, .str .x .x11 .x14 0]) u
      fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
        (∀ r, r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → u'.gpr r = u.gpr r) ∧
        u'.mem = u.mem.writeW (D + BitVec.ofNat 64 k) (u.mem.readW (S + BitVec.ofNat 64 k) 64) := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImmX_ok (d := .x13) hs hk) fun u₁ ⟨hrd₁, hwr₁, hsp₁, hm₁, h13₁, hg₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImmX_ok (d := .x14) ((hg₁ _ hd13).trans hd) hk) fun u₂ ⟨hrd₂, hwr₂, hsp₂, hm₂, h14₂, hg₂⟩ => ?_
  refine WP.mono (copyW_ok (so := 0) (d := 0) (S := S + BitVec.ofNat 64 k) (D := D + BitVec.ofNat 64 k)
    ((hg₂ _ (by decide)).trans h13₁) h14₂ ⟨rfl, by decide⟩ ⟨rfl, by decide⟩
    (by rw [add_ofNat_zero, hrd₂, hwr₂, hrd₁, hwr₁]; exact hr)
    (by rw [add_ofNat_zero, hwr₂, hwr₁]; exact hw) (by decide)) fun u' ⟨hrd, hwr, hsp, hg, hm⟩ => ?_
  rw [add_ofNat_zero, add_ofNat_zero, hm₂, hm₁] at hm
  exact ⟨hrd.trans (hrd₂.trans hrd₁), hwr.trans (hwr₂.trans hwr₁), hsp.trans (hsp₂.trans hsp₁),
    fun r h11 h13 h14 => by rw [hg r h11, hg₂ r h14, hg₁ r h13], hm⟩

/-- `copyBytes`: the `Q` bytes at `src` to `dst`, when the two ranges are apart. -/
theorem copyBytes_ok {src dst : Reg} {S D : Addr} {Q : Nat} (hdr : dst ≠ .x11) (hsr : src ≠ .x11)
    (hd13 : dst ≠ .x13) (hsep : Region.Disjoint ⟨S, Q⟩ ⟨D, Q⟩) (h8 : 8 ≤ Q) (hQ : Q < 4096) {u : State}
    (hs : u.gpr src = S) (hd : u.gpr dst = D)
    (hr : ∀ j, j + 8 ≤ Q → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 j) 8)
    (hw : ∀ j, j + 8 ≤ Q → InRegions u.wr (D + BitVec.ofNat 64 j) 8) :
    WP isa (.block (Cfg.copyBytes Q src dst)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → u'.gpr r = u.gpr r) ∧
      Frame [⟨D, Q⟩] u.mem u'.mem ∧ Spec.Sha256.bytesAt u'.mem D Q = Spec.Sha256.bytesAt u.mem S Q := by
  rw [Cfg.copyBytes, WP.block_append_iff]
  have hK : 8 * (Q / 8) ≤ Q := Nat.mul_div_le Q 8
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := add_ofNat_zero
  refine WP.mono (copyN_ok (S := S) (D := D) (so := 0) (d := 0) (K := Q / 8) hdr hsr
      (by rw [z, z]; exact (hsep.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega)))
      (by omega) ⟨rfl, by omega⟩ ⟨rfl, by omega⟩ (Q / 8) (Nat.le_refl _) u hs hd
      (fun j hj => by rw [Nat.zero_add]; exact hr (8 * j) (by omega))
      fun j hj => by rw [Nat.zero_add]; exact hw (8 * j) (by omega))
    fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hf₁, hb₁⟩ => ?_
  rw [z] at hf₁ hb₁
  rw [z] at hb₁
  have hf₁' : Frame [⟨D, Q⟩] u.mem u₁.mem :=
    hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  by_cases hm : Q % 8 = 0
  · simp only [hm, ite_true]
    have e : 8 * (Q / 8) = Q := by omega
    rw [e] at hb₁
    exact WP.block_nil ⟨hrd₁, hwr₁, hsp₁, fun r h _ _ => hg₁ r h, hf₁', hb₁⟩
  · simp only [hm, ite_false]
    refine WP.mono (copyAt_ok (u := u₁) (k := Q - 8) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd) hd13 (by omega)
      (hrd₁ ▸ hwr₁ ▸ hr (Q - 8) (by omega)) (hwr₁ ▸ hw (Q - 8) (by omega)))
      fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ?_
    have hf₂ : Frame [⟨D + BitVec.ofNat 64 (Q - 8), 8⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁,
      fun r h11 h13 h14 => (hg₂ r h11 h13 h14).trans (hg₁ r h11),
      hf₁'.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega)⟩), ?_⟩
    rw [show Q = (Q - 8) + 8 by omega, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add]
    congr 1
    · rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (by omega),
        bytesAt_take _ _ (k := 8 * (Q / 8)) (by omega), hb₁, ← bytesAt_take _ _ (by omega)]
    · rw [hm₂, bytesAt_copied]
      exact bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hsep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega)))
        (by omega)

end VG.Proof.Ecdsa.Rfc6979.AArch64
