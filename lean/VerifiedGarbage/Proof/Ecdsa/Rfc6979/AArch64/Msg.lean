module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Hmac.Common
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
import VerifiedGarbage.Proof.Mgf1.Bytes

/-! ### `Ecdsa.Rfc6979.AArch64.Copy`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on AArch64: copying words

`copyN k src so dst d` copies the `8 k` bytes at `src + so` to `dst + d`, a
word at a time through `x11`, when the two ranges are apart: each word
written is the word read (`copyW_ok`), so the bytes written are the bytes
read (`copyN_ok`, by induction on the words). `copyBytes` copies `Q` bytes,
`Q` at least 8: its words, then the last eight bytes again through `x13` and
`x14` (`copyAt_ok`) if `Q` is not a multiple of 8 (`copyBytes_ok`).
-/

@[expose] public section

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
    refine WP.mono (copyN_ok hdr hsr hsep hdn hso hdo k (by omega_arith) u hs hd hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (copyW_ok (u := u₁) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd) ⟨by omega_arith, by omega_arith⟩
      ⟨by omega_arith, by omega_arith⟩ (hrd₁ ▸ hwr₁ ▸ hr k (by omega_arith)) (hwr₁ ▸ hw k (by omega_arith)) hdr)
      fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ?_
    -- The word written, within the destination.
    have hsub : Region.Sub ⟨D + BitVec.ofNat 64 (d + 8 * k), 8⟩ ⟨D + BitVec.ofNat 64 d, 8 * K⟩ :=
      Offset.sub _ (by omega_arith) (by omega_arith)
    have hf₂ : Frame [⟨D + BitVec.ofNat 64 (d + 8 * k), 8⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (Nat.le_refl _) (by omega_arith) (by omega_arith))
    -- The word read, unchanged by the earlier words.
    have hsrc : Spec.Sha256.bytesAt u₁.mem (S + BitVec.ofNat 64 (so + 8 * k)) 8 =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 (so + 8 * k)) 8 :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep.sub_left (Offset.sub _ (by omega_arith) (by omega_arith))) (by omega_arith)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩), ?_⟩
    rw [show 8 * (k + 1) = 8 * k + 8 by omega_arith, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, Offset.add_add, ← hsrc]
    congr 1
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
    · rw [hm₂]; exact bytesAt_copied _ _ _

/-- The first `n` of `k` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : n ≤ k) :
    Spec.Sha256.bytesAt m p n = (Spec.Sha256.bytesAt m p k).take n := by
  rw [show k = n + (k - n) by omega_arith, Proof.Hmac.Common.bytesAt_add, List.take_left']
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
      (by rw [z, z]; exact (hsep.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith)))
      (by omega_arith) ⟨rfl, by omega_arith⟩ ⟨rfl, by omega_arith⟩ (Q / 8) (Nat.le_refl _) u hs hd
      (fun j hj => by rw [Nat.zero_add]; exact hr (8 * j) (by omega_arith))
      fun j hj => by rw [Nat.zero_add]; exact hw (8 * j) (by omega_arith))
    fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hf₁, hb₁⟩ => ?_
  rw [z] at hf₁ hb₁
  rw [z] at hb₁
  have hf₁' : Frame [⟨D, Q⟩] u.mem u₁.mem :=
    hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩
  by_cases hm : Q % 8 = 0
  · simp only [hm, ite_true]
    have e : 8 * (Q / 8) = Q := by omega_arith
    rw [e] at hb₁
    exact WP.block_nil ⟨hrd₁, hwr₁, hsp₁, fun r h _ _ => hg₁ r h, hf₁', hb₁⟩
  · simp only [hm, ite_false]
    refine WP.mono (copyAt_ok (u := u₁) (k := Q - 8) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd) hd13 (by omega_arith)
      (hrd₁ ▸ hwr₁ ▸ hr (Q - 8) (by omega_arith)) (hwr₁ ▸ hw (Q - 8) (by omega_arith)))
      fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ?_
    have hf₂ : Frame [⟨D + BitVec.ofNat 64 (Q - 8), 8⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁,
      fun r h11 h13 h14 => (hg₂ r h11 h13 h14).trans (hg₁ r h11),
      hf₁'.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega_arith)⟩), ?_⟩
    rw [show Q = (Q - 8) + 8 by omega_arith, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add]
    congr 1
    · rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (by omega_arith),
        bytesAt_take _ _ (k := 8 * (Q / 8)) (by omega_arith), hb₁, ← bytesAt_take _ _ (by omega_arith)]
    · rw [hm₂, bytesAt_copied]
      exact bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hsep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith)))
        (by omega_arith)


section

open VG.Proof.RsaOaep.AArch64 (count_loop counter_step counter_ne read_one byte64 byte_rt64 write1_apply)
open VG.Proof.Mgf1 (ifp ifn)

variable {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## A byte loop -/

/-- After `j` of the `n` bytes from `q` to `p`. -/
structure CpI (u₀ : State) (p q : Addr) (n j : Nat) (v : State) : Prop where
  rd : v.rd = u₀.rd
  wr : v.wr = u₀.wr
  sp : v.sp = u₀.sp
  syms : v.syms = u₀.syms
  gpr : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → v.gpr r = u₀.gpr r
  x11 : v.gpr .x11 = q + BitVec.ofNat 64 j
  x12 : v.gpr .x12 = p + BitVec.ofNat 64 j
  x13 : v.gpr .x13 = BitVec.ofNat 64 (n - j)
  mem : ∀ x, v.mem x = if (⟨p, j⟩ : Region).Contains x 1 then u₀.mem (q + (x - p)) else u₀.mem x

/-- One byte of the loop. -/
theorem cpStep_ok {v : State} {a b : Addr} (h11 : v.gpr .x11 = a) (h12 : v.gpr .x12 = b)
    (hr : InRegions (v.rd ++ v.wr) a 1) (hw : InRegions v.wr b 1) :
    WP isa (.block Cfg.cpBody) v fun v' => v'.rd = v.rd ∧ v'.wr = v.wr ∧ v'.sp = v.sp ∧ v'.syms = v.syms ∧
      v'.mem = v.mem.write b 1 (v.mem a) ∧ v'.gpr .x11 = a + BitVec.ofNat 64 1 ∧
      v'.gpr .x12 = b + BitVec.ofNat 64 1 ∧ v'.gpr .x13 = v.gpr .x13 - BitVec.ofNat 64 1 ∧
      ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → v'.gpr r = v.gpr r := by
  apply WP.of_runBlock
  simp only [Cfg.cpBody, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load, State.store,
    addr, Size.bits, Nat.mod_one, and_self, ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, BitVec.add_zero, h11, h12, hr, hw, read_one, byte64, byte_rt64,
    BitVec.setWidth_eq, show (1 : Nat) < 4096 by decide, show (0 : Nat) < 4096 by decide]
  exact ⟨by atriv, by atriv, by atriv, by atriv, by atriv, by atriv, by atriv, by atriv,
    fun r h₁ h₂ h₃ h₄ => by simp only [h₁, h₂, h₃, h₄, ite_false]⟩

theorem cpRaw_ok {u₀ : State} {p q : Addr} {n : Nat} (hn : 0 < n) (hpn : n < 2 ^ 63)
    (hw : InRegions u₀.wr p n) (hsrc : ∀ i < n, InRegions (u₀.rd ++ u₀.wr) (q + BitVec.ofNat 64 i) 1)
    (hd : ∀ i < n, ¬ (⟨p, n⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1)
    (h11 : u₀.gpr .x11 = q) (h12 : u₀.gpr .x12 = p) (h13 : u₀.gpr .x13 = BitVec.ofNat 64 n) :
    WP isa Cfg.cpLoop u₀ (CpI u₀ p q n n) := by
  refine count_loop hn (CpI u₀ p q n) (fun j hj v I => ?_)
    ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [h11, add_ofNat_zero], by rw [h12, add_ofNat_zero],
      by rw [h13, Nat.sub_zero], fun x => by simp [Region.Contains]⟩
  have hin : InRegions v.wr (p + BitVec.ofNat 64 j) 1 := by
    obtain ⟨R, hR, hc⟩ := hw
    refine ⟨R, I.wr ▸ hR, hc.byte ?_⟩
    rw [BitVec.add_comm p, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hpn, hj])]
    exact hj
  have hrd : InRegions (v.rd ++ v.wr) (q + BitVec.ofNat 64 j) 1 := by
    rw [I.rd, I.wr]; exact hsrc j hj
  have hq : v.mem (q + BitVec.ofNat 64 j) = u₀.mem (q + BitVec.ofNat 64 j) := by
    rw [I.mem, ifn]
    exact fun h => hd j hj (by
      simp only [Region.Contains] at h ⊢; omega_using [hj, h])
  refine WP.mono (cpStep_ok I.x11 I.x12 hrd hin) fun v' ⟨hrd', hwr', hsp', hsy', hm', h11', h12', h13', hg'⟩ => ?_
  refine ⟨⟨hrd'.trans I.rd, hwr'.trans I.wr, hsp'.trans I.sp, hsy'.trans I.syms,
    fun r a b c d => (hg' r a b c d).trans (I.gpr r a b c d), by rw [h11', Offset.add_add],
    by rw [h12', Offset.add_add], by rw [h13', I.x13, counter_step hj (by omega_using [hpn])], fun x => ?_⟩, ?_⟩
  · rw [hm', write1_apply, I.mem x, hq]
    by_cases he : x = p + BitVec.ofNat 64 j
    · subst he
      rw [ifp rfl, ifp (show (⟨p, j + 1⟩ : Region).Contains (p + BitVec.ofNat 64 j) 1 from
        Offset.contains_base _ (by omega_using []) (by omega_using [hpn, hj]))]
      congr 1
      rw [BitVec.add_comm p, BitVec.add_sub_cancel]
    · rw [ifn he]
      have hne : (x - p).toNat ≠ j := fun h => he (by
        rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])
      have iff : (⟨p, j + 1⟩ : Region).Contains x 1 ↔ (⟨p, j⟩ : Region).Contains x 1 := by
        simp only [Region.Contains]; omega_using [hne]
      by_cases h1 : (⟨p, j⟩ : Region).Contains x 1
      · rw [ifp h1, ifp (iff.mpr h1)]
      · rw [ifn h1, ifn (fun h => h1 (iff.mp h))]
  · rw [h13', I.x13, counter_step hj (by omega_using [hpn])]; exact counter_ne hj (by omega_using [hpn])

/-- `n` bytes from `q` (`x11`) to `p` (`x12`), `n` in `x13`, by `cpLoop`:
`Ctx` kept, for a destination the code may write apart from the source. -/
theorem cp_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {p q : Addr} {n : Nat} (hn : 0 < n)
    (hn' : n < 2 ^ 63) (h13 : u.gpr .x13 = BitVec.ofNat 64 n) (h12 : u.gpr .x12 = p) (h11 : u.gpr .x11 = q)
    (hpn : p.toNat + n ≤ 2 ^ 64) (hw : InRegions u.wr p n)
    (hs : Safe L ⟨p, n⟩) (hsrc : ∀ i < n, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 i) 1)
    (hd : ∀ i < n, ¬ (⟨p, n⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1) :
    WP isa Cfg.cpLoop u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → u'.gpr r = u.gpr r) ∧
      Frame [⟨p, n⟩] u.mem u'.mem ∧ Spec.Sha256.bytesAt u'.mem p n = Spec.Sha256.bytesAt u.mem q n := by
  refine WP.mono (cpRaw_ok hn hn' hw hsrc hd h11 h12 h13) fun u' I => ?_
  have hf : Frame [⟨p, n⟩] u.mem u'.mem := fun x hx => by
    rw [I.mem x, ifn (hx _ (List.mem_singleton_self _))]
  refine ⟨hc.keep hL I.rd I.wr I.sp
      (fun r hr _ => I.gpr r (ne_cs hr (by decide)) (ne_cs hr (by decide)) (ne_cs hr (by decide))
        (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs) I.syms, I.gpr, hf, ?_⟩
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [I.mem, ifp (Offset.contains_base _ (d := i) (by omega) (by omega)), BitVec.add_comm p, BitVec.add_sub_cancel]

end

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end

/-!
# Deterministic ECDSA on AArch64: the messages of steps d, f and h.3

The byte `b`, and `‖ d ‖ h` if `full`, at `scratch + 2256` (`msg_ok`), as on
x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Msg.lean`): the byte (`strb_ok`), then
the private key and `h`, `Q` bytes each, copied (`tail_ok`) through `x12`,
which points after `b`, by `copyBytes` (`copyB_ok`). HMAC's text is `V` (`D`
bytes, from the frame, the table's `update` with it), then this message.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The pointers: `scratch` in `x9`, `d` in `x10` and the frame in `x15`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .x9 = L.scr ∧
      u.gpr .x10 = L.d ∧ u.gpr .x15 = L.B + BitVec.ofNat 64 16 := by
  have h200 := hc.inFr (d := 200) (by omega_arith) (by omega_arith)
  have h216 := hc.inFr (d := 216) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [Cfg.msgPtrs, fScratch, fD, runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceMod,
    Nat.reduceLT, and_self, ite_true, State.load, RegUpd.gpr_write, RegUpd.sp_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.mem_write, reduceCtorEq, ite_false, hc.sp, Offset.add_add, Nat.reduceAdd, h200,
    h216, Option.map_some, read8, hc.pScr, hc.pD, BitVec.setWidth_eq, show (0 : Nat) < 4096 by decide,
    BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨hc.regs hL rfl rfl rfl rfl (fun r hr h30 => ?_) rfl, trivial⟩
  have h₁ : r ∉ [Reg.x9, .x10, .x15] := not_pres hr _ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h₁
  simp only [RegUpd.gpr_write, h₁.1, h₁.2.1, h₁.2.2, ite_false]

theorem byte_self (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v a = v := by
  simp only [Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero, Nat.zero_lt_one, ite_true]
  exact BitVec.extractLsb'_eq_self

theorem movzb (b : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 64 (BitVec.ofNat 16 b) <<< (16 * 0)))) =
      BitVec.ofNat 8 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- The byte `b` stored at `scratch + o`, through `x9`. -/
theorem strb_ok {u : State} (hc : Ctx L g m₀ u) (h9 : u.gpr .x9 = L.scr) {b o : Nat} (ho : o < 4096) :
    WP isa (.block [.movz .x .x11 (BitVec.ofNat 16 b) 0, .strb .x11 .x9 o]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.write (L.scr + BitVec.ofNat 64 o) 1 (BitVec.ofNat 8 b) := by
  have w := hc.inScrW (o := o) (n := 1) (by omega_arith)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide, ite_true,
    addr, Nat.mod_one, ho, and_self, Option.bind_some, State.store, State.read, Size.bits, RegUpd.gpr_write,
    RegUpd.wr_write, RegUpd.mem_write, reduceCtorEq, ite_false, h9, w, Option.some.injEq,
    exists_eq_left']
  refine ⟨by atriv, by atriv, by atriv, fun r hr => ?_, by rw [movzb]⟩
  simp only [hr, ite_false]

/-- The bytes of a zero word. -/
theorem bytesAt_writeW_zero64 (m : Mem) (p : Addr) {k : Nat} (hk : k ≤ 8) :
    Spec.Sha256.bytesAt (m.writeW p (0 : BitVec 64)) p k = List.replicate k 0 := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [Spec.Sha256.bytesAt], fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have e : (p + BitVec.ofNat 64 i - p).toNat = i := by
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  simp only [Mem.writeW, Mem.write, e, show i < 64 / 8 by omega_arith, ite_true]
  apply BitVec.eq_of_toNat_eq; simp

/-- `d ← src + k`. -/
theorem addImm_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d src : Reg} (hd : d ∉ preserved) {S : Addr}
    (hs : u.gpr src = S) {k : Nat} (hk : k < 4096) :
    WP isa (.block [.addImm .x d src k]) u (Upd L g m₀ u d (S + BitVec.ofNat 64 k)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hk, ite_true, State.read, Size.bits,
    BitVec.setWidth_eq, hs, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- A word stored at `dst + d`. -/
theorem strW_ok {u : State} {t dst : Reg} {D : Addr} (hd : u.gpr dst = D) {d : Nat}
    (hdo : d % 8 = 0 ∧ d < 32768) (hw : InRegions u.wr (D + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.str .x t dst d]) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.gpr = u.gpr ∧ u'.syms = u.syms ∧ u'.mem = u.mem.writeW (D + BitVec.ofNat 64 d) (u.gpr t) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, hdo, and_self, ite_true,
    Option.bind_some, State.store, State.read, Size.bits, BitVec.setWidth_eq, hd, hw, write8,
    Option.some.injEq, exists_eq_left']

/-- `copyBytes`: `len` bytes copied from `S` to `scratch + e`, with `Ctx` kept. -/
theorem copyB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src dst : Reg} {S : Addr} {e len : Nat}
    (hs : u.gpr src = S) (hdi : u.gpr dst = L.scr + BitVec.ofNat 64 e) (hsr : src ≠ .x11) (hdr : dst ≠ .x11)
    (hd13 : dst ≠ .x13) (h8 : 8 ≤ len) (hl : len ≤ 72) (he : e + len ≤ 8192)
    (hr : ∀ j, j + 8 ≤ len → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 j) 8)
    (hsep : Region.Disjoint ⟨S, len⟩ ⟨L.scr + BitVec.ofNat 64 e, len⟩) :
    WP isa (.block (Cfg.copyBytes len src dst)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 e, len⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 e) len = Spec.Sha256.bytesAt u.mem S len :=
  WP.mono_syms (copyBytes_ok hdr hsr hd13 hsep h8 (by omega_arith) hs hdi hr
    fun j hj => by rw [Offset.add_add]; exact hc.inScrW (by omega_arith)) fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ hsy =>
    ⟨hc.keep hL hrd hwr hsp (fun r hr _ => hg r (ne_cs hr (by decide)) (ne_cs hr (by decide))
      (ne_cs hr (by decide))) hf (hsy := hsy)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L he), hg, hf, hb⟩

/-- `‖ d ‖ h`, `Q` bytes each, after the byte at `scratch + 2256`, with
`scratch` in `x9`, `d` in `x10` and the frame in `x15` (`h` at `ho` in it),
by `copyBytes` through `x12` and through `x13` and `x14`. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h9 : u.gpr .x9 = L.scr) (h10 : u.gpr .x10 = L.d)
    (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16) {Q ho : Nat} (h8 : 8 ≤ Q) (hQ : Q ≤ 66)
    (hho : 16 + ho + Q ≤ 240 + 8 * L.e) (hho' : ho < 4096) (hq : Q ≤ L.q) :
    WP isa (.block (.addImm .x .x12 .x9 (sMsg + 1) :: Cfg.copyBytes Q .x10 .x12 ++
        ([.addImm .x .x13 .x15 ho, .addImm .x .x14 .x12 Q] : List Instr) ++ Cfg.copyBytes Q .x13 .x14)) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 2257, 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 2257) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++ Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + ho)) Q := by
  have he := L.he
  simp only [sMsg]
  rw [List.cons_append, List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok hL hc (d := .x12) (src := .x9) (by decide) h9 (k := 2256 + 1) (by omega_arith))
    fun u₁ h₁ => ?_
  rw [← h₁.mem]
  -- `d`'s bytes, then `h`'s, each copied from where nothing written since is.
  have dS : Region.Disjoint ⟨L.d, Q⟩ ⟨L.scr + BitVec.ofNat 64 (2256 + 1), Q⟩ :=
    (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_arith))
  have hS : ∀ {m m' : Mem} {e : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 e, Q⟩] m m' → e + Q ≤ 8192 →
      Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 (16 + ho)) Q =
        Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (16 + ho)) Q :=
    fun hf he => bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith)
  have fr : ∀ {m₁ m₂ m₃ : Mem}, Frame [⟨L.scr + BitVec.ofNat 64 (2256 + 1), Q⟩] m₁ m₂ →
      Frame [⟨L.scr + BitVec.ofNat 64 (2256 + 1 + Q), Q⟩] m₂ m₃ →
      Frame [⟨L.scr + BitVec.ofNat 64 2257, 2 * Q⟩] m₁ m₃ := fun f₁ f₂ =>
    (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩).trans
    (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩)
  have cat : ∀ {m₂ m₃ : Mem}, Frame [⟨L.scr + BitVec.ofNat 64 (2256 + 1 + Q), Q⟩] m₂ m₃ →
      Spec.Sha256.bytesAt m₃ (L.scr + BitVec.ofNat 64 2257) (2 * Q) =
        Spec.Sha256.bytesAt m₂ (L.scr + BitVec.ofNat 64 (2256 + 1)) Q ++
          Spec.Sha256.bytesAt m₃ (L.scr + BitVec.ofNat 64 (2256 + 1 + Q)) Q := fun f₂ => by
    rw [show 2 * Q = Q + Q by omega_arith, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyB_ok hL h₁.ctx (u := u₁) (src := .x10) (dst := .x12) (e := 2256 + 1) (len := Q)
    (by rw [h₁.keep _ (by decide), h10]) h₁.val (by decide) (by decide) (by decide) h8 (by omega_arith) (by omega_arith)
    (fun j hj => h₁.ctx.inD (by omega_arith) (by omega_arith)) dS) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addImm_ok hL hc₂ (d := .x13) (src := .x15) (by decide)
    (by rw [hg₂ _ (by decide) (by decide) (by decide), h₁.keep _ (by decide), h15]) (k := ho) hho')
    fun u₃ h₃ => ?_
  refine WP.mono (addImm_ok hL h₃.ctx (d := .x14) (src := .x12) (by decide)
    (by rw [h₃.keep _ (by decide), hg₂ _ (by decide) (by decide) (by decide), h₁.val]) (k := Q) (by omega_arith))
    fun u₄ h₄ => ?_
  rw [Offset.add_add] at h₃ h₄
  refine WP.mono (copyB_ok hL h₄.ctx (src := .x13) (dst := .x14) (S := L.B + BitVec.ofNat 64 (16 + ho))
    (e := 2256 + 1 + Q) (len := Q)
    (by rw [h₄.keep _ (by decide)]; exact h₃.val) h₄.val (by decide) (by decide) (by decide) h8 (by omega_arith)
    (by omega_arith)
    (fun j hj => by rw [Offset.add_add]; exact h₄.ctx.inFr (by omega_arith) (by omega_arith))
    (hL.stk_scr (by omega_arith) (by omega_arith))) fun u₅ ⟨hc₅, _, hf₅, hb₅⟩ => ?_
  rw [h₄.mem, h₃.mem] at hf₅ hb₅
  refine ⟨hc₅, fr hf₂ hf₅, ?_⟩
  rw [cat hf₅, hb₂, hb₅, hS hf₂ (by omega_arith)]

variable {P : RfcHash}

/-- `h` in the frame. -/
abbrev hOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (16 + (cfgOf P).fHo)) P.Q

/-- The length of the message. -/
abbrev mlen (P : RfcHash) (full : Bool) : Nat := if full then 1 + 2 * P.Q else 1

/-- The message `b` (`‖ d ‖ h` if `full`, `Q` bytes each) at `scratch + 2256`. -/
theorem msg_ok (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g m₀ t) (h9 : t.gpr .x9 = L.scr)
    (h10 : t.gpr .x10 = L.d) (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16) (b : Nat) (full : Bool) :
    WP isa (.block ((cfgOf P).msg b full)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (mlen P full) =
        [BitVec.ofNat 8 b] ++ (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else []) := by
  have hQ := P.sizes
  have he := L.he
  have hho : 16 + (cfgOf P).fHo + P.Q ≤ 240 + 8 * L.e ∧ (cfgOf P).fHo < 4096 := by
    simp only [Cfg.fHo, cfgOf]
    rcases Bool.eq_false_or_eq_true P.R.big with h | h <;>
      simp only [h, fX, fH, ite_true, ite_false, Bool.false_eq_true] <;> exact ⟨by anums, by decide⟩
  have hb : ∀ {u : State}, Ctx L g m₀ u → u.gpr .x9 = L.scr →
      WP isa (.block [.movz .x .x11 (BitVec.ofNat 16 b) 0, .strb .x11 .x9 sMsg]) u fun u' => Ctx L g m₀ u' ∧
        (∀ r, r ≠ .x11 → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 2256) 1 = [BitVec.ofNat 8 b] := fun {u} hcu h9u =>
    WP.mono_syms (strb_ok hcu h9u (b := b) (o := 2256) (by decide)) fun u' ⟨hrd, hwr, hsp, hg, hm⟩ hsy => by
      have hf : Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] u.mem u'.mem := by
        rw [hm]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
      refine ⟨hcu.keep hL hrd hwr hsp (fun r hr _ => hg r (ne_cs hr (by decide))) hf (hsy := hsy)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by decide)), hg, hf, ?_⟩
      show [u'.mem (L.scr + BitVec.ofNat 64 2256 + BitVec.ofNat 64 0)] = _
      rw [add_ofNat_zero, hm, byte_self]
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil, mlen]
    refine WP.mono (hb hc h9) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega_arith)
  · simp only [Cfg.msg, ite_true, mlen]
    rw [WP.block_append_iff]
    refine WP.mono (hb hc h9) fun u ⟨hcu, hg, hf, hb⟩ => ?_
    refine WP.mono (tail_ok hL hcu ((hg _ (by decide)).trans h9) ((hg _ (by decide)).trans h10)
      ((hg _ (by decide)).trans h15) (Q := (cfgOf P).len) (ho := (cfgOf P).fHo)
      (by show 8 ≤ P.Q; anums) (by show P.Q ≤ 66; anums) hho.1 hho.2 (by rw [hq]; rfl))
      fun u' ⟨hcu', hf', hb'⟩ => ?_
    have hlen : (cfgOf P).len = P.Q := rfl
    rw [hlen] at hf' hb'
    refine ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by omega_arith)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [Proof.Hmac.Common.bytesAt_add _ _ 1 (2 * P.Q), Offset.add_add]
      have hb'' : Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 2257) (2 * P.Q) =
          Spec.Sha256.bytesAt u.mem L.d P.Q ++ hOf P L u.mem := hb'
      rw [hb'', bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by anums)) (by omega_arith), hb]
      refine congrArg ([BitVec.ofNat 8 b] ++ ·) ?_
      have hdq : Spec.Sha256.bytesAt u.mem L.d P.Q = Spec.Sha256.bytesAt t.mem L.d P.Q :=
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix (by rw [hq]))).sub_right (Offset.sub_base _ (by omega_arith)))
          (by anums)
      rw [hdq]
      refine congrArg (Spec.Sha256.bytesAt t.mem L.d P.Q ++ ·) ?_
      exact bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by omega_arith) (by omega_arith)) (by anums)

end VG.Proof.Ecdsa.Rfc6979.AArch64
