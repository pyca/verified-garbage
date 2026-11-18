module

public import VerifiedGarbage.Proof.AesSiv.Long
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesSiv.CtrPart
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Mac
import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
import VerifiedGarbage.Proof.Cmac.RISCV64.Dbl
import VerifiedGarbage.Proof.Siv.Spec
public import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes

/-! ### `AesSiv.RISCV64.Short`, which this module and modules that import it used -/

section

/-! ### `AesSiv.RISCV64.S2v`, which this module and modules that import it used -/

section

/-!
# AES-SIV on RISC-V: S2V over the components of associated data

Untrusted: everything here is checked by Lean. S2V starts with
`D = AES-CMAC(K1, <zero>)`, a finalization of the zero block at `W + 16`
from a zero state at `W + 256` (`start_wp`). The `N` descriptors at `A`
(16 bytes each: an address and a length) list the components in the memory
`m` (`descW`, `Ads`). Each iteration of `s2vAds` loads the next descriptor,
little-endian a byte at a time (`adNext`), computes the CMAC of its
component into the state at `W + 240` (`cmacOf_wp`) and folds it into `D`
(`adStep_wp`: `dbl` a byte at a time, `Proof.Cmac.RISCV64.dbl_wp`, then the
XOR of two blocks of `W`, `xor16_wp`), so `D` is S2V's state of the
components so far (`AInv`, `aStep_wp`), and of all of them after the loop
(`s2vAds_wp`). The code writes only within `W` from byte 16 to 128 and from
byte 240 on (`wR`). As on PPC64LE (`Proof/AesSiv/PPC64LE/S2v.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64
open VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.CmacAes.Stream.RISCV64 (FArgs)
open VG.Spec.Aes (bytesAt)

/-- What S2V writes: `W` from byte 16 to 128 and from byte 240 on. -/
abbrev wR (c : Cx) : List Region := [⟨c.W + BitVec.ofNat 64 16, 112⟩, ⟨c.W + BitVec.ofNat 64 240, 2336⟩]

theorem macR_wR {c : Cx} {st : Nat} (h : 240 ≤ st) (h' : st + 16 ≤ 384) :
    ∀ r ∈ macR c st, ∃ r' ∈ wR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ h (by omega_using [h'])⟩
  · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ (by decide) (by decide)⟩

theorem w16_wR {c : Cx} {d : Nat} (h : 240 ≤ d ∨ (16 ≤ d ∧ d + 16 ≤ 128)) (h' : d + 16 ≤ 2576) :
    ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 d, 16⟩ : Region)], ∃ r' ∈ wR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rcases h with h | ⟨h₁, h₂⟩
  · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ h (by omega_using [h'])⟩
  · exact ⟨⟨c.W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ h₁ (by omega_using [h₂])⟩

/-- A region apart from `W` is apart from `wR`. -/
theorem dis_wR {c : Cx} {r : Region} (hw : r.Disjoint ⟨c.W, 2576⟩) : ∀ r' ∈ wR c, r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))

/-! ## XORing two blocks of `W` -/

/-- `xor16 a b d`: the blocks at `W + a` and `W + b` XORed into `W + d`, a
doubleword at a time (`Proof.Cmac.xor2Mem`). -/
theorem xor16_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {a b d : Nat} (ha : a + 16 ≤ 2048)
    (hb : b + 16 ≤ 2048) (hd : d + 16 ≤ 2048) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hd8 : d % 8 = 0)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', PK s s' → (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) →
      s'.mem = Proof.Cmac.xor2Mem s.mem (c.W + BitVec.ofNat 64 d) (c.W + BitVec.ofNat 64 a)
        (c.W + BitVec.ofNat 64 b) → WP isa (.block is) s' Q) :
    WP isa (.block (xor16 a b d ++ is)) s Q := by
  simp only [xor16, List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 a) (by omega_using [ha]) (by rw [E.s1]) (L.alW ha8 (by omega_using [ha]))
    (E.perm.wR (by omega_using [ha])) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 b) (by omega_using [hb]) (by rw [u₁.other _ (by decide), E.s1])
    (L.alW hb8 (by omega_using [hb])) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by omega_using [hb])) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 d) (by omega_using [hd])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s1])
    (L.alW hd8 (by omega_using [hd])) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by omega_using [hd])) fun s₄ u₄ => ?_
  obtain g₄ : s₄.gpr .s1 = c.W := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s1]
  obtain rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_ld (a := c.W + BitVec.ofNat 64 a + BitVec.ofNat 64 8) (by omega_using [ha]) (by rw [g₄, Offset.add_add])
    (by rw [Offset.add_add]; exact L.alW (by omega_using [ha8]) (by omega_using [ha]))
    (by rw [rd₄, wr₄, Offset.add_add]; exact E.perm.wR (by omega_using [ha])) fun s₅ u₅ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 b + BitVec.ofNat 64 8) (by omega_using [hb])
    (by rw [u₅.other _ (by decide), g₄, Offset.add_add])
    (by rw [Offset.add_add]; exact L.alW (by omega_using [hb8]) (by omega_using [hb]))
    (by rw [u₅.rd, u₅.wr, rd₄, wr₄, Offset.add_add]; exact E.perm.wR (by omega_using [hb])) fun s₆ u₆ => ?_
  refine wp_xor fun s₇ u₇ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 d + BitVec.ofNat 64 8) (by omega_using [hd])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g₄, Offset.add_add])
    (by rw [Offset.add_add]; exact L.alW (by omega_using [hd8]) (by omega_using [hd]))
    (by rw [u₇.wr, u₆.wr, u₅.wr, wr₄, Offset.add_add]; exact E.perm.wW (by omega_using [hd])) fun s₈ u₈ => ?_
  obtain hreg : ∀ r, r ≠ .t0 → r ≠ .t1 → s₈.gpr r = s.gpr r := fun r h0 h1 => by
    rw [u₈.gpr, u₇.other _ h0, u₆.other _ h1, u₅.other _ h0, u₄.gpr, u₃.other _ h0, u₂.other _ h1,
      u₁.other _ h0]
  refine k s₈ ⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄], by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp],
    fun r hr => hreg r (fun e => by subst e; exact absurd hr (by decide))
      (fun e => by subst e; exact absurd hr (by decide))⟩ hreg ?_
  simp only [u₈.mem, u₇.gpr, u₇.mem, u₆.gpr, u₆.other .t0 (by decide), u₆.mem, u₅.gpr, u₅.mem, u₄.mem,
    u₃.gpr, u₃.mem, u₂.gpr, u₂.other .t0 (by decide), u₂.mem, u₁.gpr, u₁.mem]
  rfl

/-! ## S2V's first state -/

/-- `startPre`: the zero block and `D` zeroed, and the arguments of the
finalization of the zero block. -/
theorem startPre_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block startPre) s fun s' => MacKeep s s' ∧
      s'.mem = Proof.Cmac.zero2 (Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 zO)) (c.W + BitVec.ofNat 64 dO) ∧
      FArgs s' c.C (c.W + BitVec.ofNat 64 dO) (c.W + BitVec.ofNat 64 zO) (c.W + BitVec.ofNat 64 384) 16 c.R := by
  simp only [startPre, List.append_assoc]
  refine zero16_wp L E (d := zO) (by decide) (by decide) fun s₁ pk₁ g₁ m₁ => ?_
  obtain E₁ := E.of_pk pk₁
  refine zero16_wp L E₁ (d := dO) (by decide) (by decide) fun s₂ pk₂ g₂ m₂ => ?_
  obtain E₂ := E₁.of_pk pk₂
  unfold macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by decide) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_addi (by decide) fun t₅ v₅ =>
    wp_li (by decide) fun t₆ v₆ => WP.block_nil ?_
  obtain K : MacKeep s₂ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
  obtain K₀ : MacKeep s s₂ := ⟨pk₁.trans pk₂, by rw [g₂ _ (by decide), g₁ _ (by decide)],
    by rw [g₂ _ (by decide), g₁ _ (by decide)], by rw [g₂ _ (by decide), g₁ _ (by decide)],
    by rw [g₂ _ (by decide), g₁ _ (by decide)]⟩
  obtain E₆ := E₂.of_pk K.pk
  refine ⟨K₀.trans K, by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, m₂, m₁], ?_⟩
  exact fargs L E₆ (y := dO) (by decide) (Nat.le_refl 16) (L.srcW E₆.perm (t := zO) (k := 16) (by decide))
    (L.w_w (.inl (by decide)) (by decide) (by decide))
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E₂.s2])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E₂.s3])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E₂.s1])
    (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₂.s1])
    (by rw [v₆.gpr])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₂.s1]; rfl)

theorem siv_zero : Spec.Siv.zero = Spec.Cmac.zeros 16 := rfl

/-- `D = AES-CMAC(K1, <zero>)`, S2V's first state, at `W + 256`. -/
theorem start_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.seq (.block startPre) Impl.CmacAes.Stream.RISCV64.finCall) s fun s' => MacKeep s s' ∧
      Frame (wR c) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 dO) 16 = Spec.Siv.s2vStart (Spec.Siv.ctxMac s.mem c.C c.R) := by
  have hRb := L.rb
  refine WP.seq (WP.mono (startPre_wp L E) fun s₁ ⟨K₁, m₁, F⟩ => ?_)
  refine WP.mono (fin_call_raw F) fun s₂ h₂ => ?_
  obtain f₁ : Frame (wR c) s.mem s₁.mem := by
    rw [m₁]
    exact ((Proof.Cmac.frame_store2 _ _ _).sub (w16_wR (.inr ⟨by decide, by decide⟩) (by decide))).trans
      ((Proof.Cmac.frame_store2 _ _ _).sub (w16_wR (.inl (by decide)) (by decide)))
  refine ⟨K₁.trans (MacKeep.ofSaved h₂.rd h₂.wr h₂.sp h₂.saved),
    f₁.trans (h₂.frame.sub (macR_wR (st := dO) (by decide) (by decide))), ?_⟩
  -- What the call reads.
  obtain dC : ∀ {d k : Nat}, d + k ≤ 512 → ∀ r ∈ wR c, (⟨c.C + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd => dis_wR (L.c_w.sub_left (Lay.cSub hd))
  have cK {d k : Nat} (hd : d + k ≤ 512) :
      bytesAt s₁.mem (c.C + BitVec.ofNat 64 d) k = bytesAt s.mem (c.C + BitVec.ofNat 64 d) k :=
    Proof.Cmac.bytesAt_frame f₁ (dC hd) (by omega_using [hd])
  obtain sch := cK (d := 0) (k := 16 * (c.R + 1)) (by omega_using [hRb])
  rw [BitVec.add_zero] at sch
  obtain hz : bytesAt s₁.mem (c.W + BitVec.ofNat 64 zO) 16 = Spec.Cmac.zeros 16 := by
    obtain fz : Frame [⟨c.W + BitVec.ofNat 64 dO, 16⟩] (Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 zO))
        (Proof.Cmac.zero2 (Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 zO)) (c.W + BitVec.ofNat 64 dO)) :=
      Proof.Cmac.frame_store2 _ _ _
    obtain dz : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 dO, 16⟩ : Region)],
        (⟨c.W + BitVec.ofNat 64 zO, 16⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    rw [m₁, Proof.Cmac.bytesAt_frame fz dz (by decide), Proof.Cmac.zero2_bytes]
  obtain hd : bytesAt s₁.mem (c.W + BitVec.ofNat 64 dO) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero2_bytes]
  rw [h₂.out, Proof.CmacAes.RISCV64.mn, Proof.CmacAes.RISCV64.ciphAt, sch, cK (d := 240) (k := 16) (by decide),
    cK (d := 256) (k := 16) (by decide), hz, hd, Spec.Siv.s2vStart, Spec.Siv.ctxMac, Spec.Siv.schedCiph,
    Siv.macWith_chained, siv_zero]
  rfl

/-! ## The descriptors -/

/-- An access within a region the permissions cover, for a region of at
most `2⁶⁴` bytes. -/
theorem in_off_le {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k ≤ 2 ^ 64) (hn : 0 < n) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  h _ _ ⟨_, List.mem_singleton_self _, by
    simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hd, hk, hn])]
    exact hd⟩

/-- Word `j` (0: the address, 1: the length) of descriptor `i` at `A`, in `m`. -/
abbrev descW (m : Mem) (A : Addr) (i j : Nat) : BitVec 64 := m.readW (A + BitVec.ofNat 64 (16 * i + 8 * j)) 64

/-- The `i`-th component, `i < N`. -/
theorem components_getElem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (Spec.Siv.components 64 m A N)[i]'(by simp [Spec.Siv.components, Sig.listed, hi]) =
      bytesAt m (descW m A i 0) (descW m A i 1).toNat := by
  simp only [Spec.Siv.components, Sig.listed, List.getElem_map, List.getElem_range, Elem.size, Nat.mul_one,
    descW, BitVec.setWidth_eq]
  rw [show i * (2 * (64 / 8)) = 16 * i + 8 * 0 by omega_using [], show (64 / 8 : Nat) = 8 from rfl, Offset.add_add,
    show 16 * i + 8 * 0 + 8 = 16 * i + 8 * 1 by omega_using []]

theorem length_components (m : Mem) (p : Addr) (N : Nat) : (Spec.Siv.components 64 m p N).length = N := by
  simp [Spec.Siv.components, Sig.listed]

theorem s2vAcc_snoc (mac : List Byte → List Byte) (xs : List (List Byte)) (x : List Byte) :
    Spec.Siv.s2vAcc mac (xs ++ [x]) = Spec.Siv.s2vStep mac (Spec.Siv.s2vAcc mac xs) x := by
  simp [Spec.Siv.s2vAcc, List.foldl_append]

/-- The components the descriptors list in `m`, each a buffer the code may
read. -/
abbrev Ads (c : Cx) (m : Mem) (s : State) : Prop :=
  ∀ i < c.N, Buf c s (descW m c.A i 0) (descW m c.A i 1).toNat

theorem Ads.of_eq {c : Cx} {m : Mem} {s s' : State} (h : Ads c m s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Ads c m s' := fun i hi => (h i hi).of_eq hrd hwr

/-! ## The loop -/

/-- Before the `i`-th component (and, for `i = N`, after the last), from the
state `σ` with the memory `m` before S2V: `D` is S2V's state of the first
`i`, `s4` and `s5` the next descriptor's address and how many are left. -/
structure AInv (c : Cx) (σ : State) (i : Nat) (s : State) : Prop where
  env : Env c s
  pk : PK σ s
  ads : Ads c σ.mem s
  s4 : s.gpr .s4 = c.A + BitVec.ofNat 64 (16 * i)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (c.N - i)
  frame : Frame (wR c) σ.mem s.mem
  acc : bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac σ.mem c.C c.R) ((Spec.Siv.components 64 σ.mem c.A c.N).take i)

/-- What `adNext` keeps. -/
structure NextKeep (s s' : State) : Prop where
  pk : PK s s'
  s4 : s'.gpr .s4 = s.gpr .s4
  s5 : s'.gpr .s5 = s.gpr .s5
  mem : s'.mem = s.mem

/-- `adNext`: the address and the length of descriptor `i`'s component in
`s6` and `s7`, each read little-endian a byte at a time (`loadLE64_ok`). -/
theorem adNext_wp {c : Cx} (L : Lay c) {σ s : State} {i : Nat} (h : AInv c σ i s) (hi : i < c.N) :
    WP isa (.block adNext) s fun s' => s'.gpr .s6 = descW σ.mem c.A i 0 ∧
      s'.gpr .s7 = descW σ.mem c.A i 1 ∧ NextKeep s s' := by
  have aw := L.aw
  obtain dA : ∀ {d : Nat}, d + 8 ≤ 16 * c.N → ∀ r ∈ wR c, (⟨c.A + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r :=
    fun hd => dis_wR (L.a_w.sub_left (Offset.sub_base _ hd))
  obtain off : ∀ {j : Nat}, s.gpr .s4 + BitVec.ofNat 64 j = c.A + BitVec.ofNat 64 (16 * i + j) := fun {j} => by
    rw [h.s4, Offset.add_add]
  obtain v₀ : s.mem.readW (c.A + BitVec.ofNat 64 (16 * i + 8 * 0)) 64 = descW σ.mem c.A i 0 :=
    (h.frame.readW (r := ⟨c.A + BitVec.ofNat 64 (16 * i + 8 * 0), 8⟩) (Region.contains_self _ _)
      (dA (by omega_using [hi])) (by decide))
  obtain v₁ : s.mem.readW (c.A + BitVec.ofNat 64 (16 * i + 8 * 1)) 64 = descW σ.mem c.A i 1 :=
    (h.frame.readW (r := ⟨c.A + BitVec.ofNat 64 (16 * i + 8 * 1), 8⟩) (Region.contains_self _ _)
      (dA (by omega_using [hi])) (by decide))
  unfold adNext
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.loadLE64_ok (d := .s6) (tmp := .t0) (hi := .t1) (n := .s4)
    (off := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [off]; exact in_off_le h.env.perm.a (by omega_using [hi]) (by omega_using [aw]) (by decide))
    (by rw [off]; exact in_off_le h.env.perm.a (by omega_using [hi]) (by omega_using [aw]) (by decide)))
    fun s₁ ⟨g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  obtain s4₁ : s₁.gpr .s4 = s.gpr .s4 := o₁ _ (by decide) (by decide) (by decide)
  refine WP.mono (Bytes.loadLE64_ok (d := .s7) (tmp := .t0) (hi := .t1) (n := .s4)
    (off := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [rd₁, wr₁, s4₁, off]; exact in_off_le h.env.perm.a (by omega_using [hi]) (by omega_using [aw]) (by decide))
    (by rw [rd₁, wr₁, s4₁, off]; exact in_off_le h.env.perm.a (by omega_using [hi]) (by omega_using [aw]) (by decide)))
    fun s₂ ⟨g₂, o₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  obtain keep : ∀ r, r ≠ .s6 → r ≠ .s7 → r ≠ .t0 → r ≠ .t1 → s₂.gpr r = s.gpr r := fun r h6 h7 h0 h1 => by
    rw [o₂ r h7 h0 h1, o₁ r h6 h0 h1]
  refine ⟨?_, ?_, ⟨⟨by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁], fun r hr => keep r
      (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))
      (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))⟩,
    keep _ (by decide) (by decide) (by decide) (by decide), keep _ (by decide) (by decide) (by decide) (by decide),
    by rw [m₂, m₁]⟩⟩
  · rw [o₂ _ (by decide) (by decide) (by decide), g₁, off, ← v₀]
  · rw [g₂, m₁, s4₁, off, ← v₁]

/-! ## The context's PRF and cipher, after writes apart from it -/

theorem ctxMac_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxMac m' C R = Spec.Siv.ctxMac m C R := by
  unfold Spec.Siv.ctxMac Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega_using [hR]))) (by omega_using [hR]),
    Proof.Cmac.bytesAt_frame hf (p := C + 240)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 240) (n := 16) (by decide))) (by decide),
    Proof.Cmac.bytesAt_frame hf (p := C + 256)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 256) (n := 16) (by decide))) (by decide)]

theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxCiph m' C R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (p := C + 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega_using [hR]))) (by omega_using [hR])]

/-! ## A step of the loop -/

/-- `adStep`: `D = dbl(D) ⊕` the CMAC state (`dbl` a byte at a time, then
the XOR a doubleword at a time); the next descriptor, and one fewer left. -/
theorem adStep_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {i k : Nat} (hk : 1 ≤ k) (hk64 : k < 2 ^ 64)
    (h17 : s.gpr .s4 = c.A + BitVec.ofNat 64 (16 * i)) (h18 : s.gpr .s5 = BitVec.ofNat 64 k) :
    WP isa (.block adStep) s fun s' => PK s s' ∧ s'.gpr .s4 = c.A + BitVec.ofNat 64 (16 * (i + 1)) ∧
      s'.gpr .s5 = BitVec.ofNat 64 (k - 1) ∧
      Frame [⟨c.W + BitVec.ofNat 64 dO, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 dO) 16 =
        Spec.Cmac.xor (Spec.Cmac.dbl 16 (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16))
          (bytesAt s.mem (c.W + BitVec.ofNat 64 stO) 16) := by
  have ww := L.ww
  unfold adStep
  rw [List.append_assoc]
  refine Proof.Cmac.RISCV64.dbl_wp (K := c.W) (src := dO) (dst := dO) (by decide) (by decide)
    Proof.Cmac.RISCV64.dbl_spec16 E.s1 (.inl rfl) (by decide) (by decide) (by simp only [dO]; omega_using [ww])
    (fun j hj => E.perm.wR (by simp only [dO]; omega_using [hj])) (fun j hj => E.perm.wW (by simp only [dO]; omega_using [hj]))
    fun s₁ g₁ rd₁ wr₁ sp₁ f₁ b₁ => ?_
  obtain pk₁ : PK s s₁ := ⟨rd₁, wr₁, sp₁, fun r hr => g₁ r (fun e => by subst e; exact absurd hr (by decide))
    (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))
    (fun e => by subst e; exact absurd hr (by decide))⟩
  obtain E₁ := E.of_pk pk₁
  refine xor16_wp L E₁ (a := dO) (b := stO) (d := dO) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun s₂ pk₂ g₂ m₂ => ?_
  refine wp_addi (by decide) fun s₃ u₃ => wp_subi (imm := 1) (by decide) fun s₄ u₄ =>
    WP.block_nil ⟨pk₁.trans (pk₂.trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄))), ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, g₂ _ (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide), h17, Offset.add_add]
    congr 2
  · rw [u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide), h18]
    exact ofNat_sub' hk hk64
  · rw [u₄.mem, u₃.mem, m₂]
    exact f₁.trans (Proof.Cmac.xor2Mem_frame _ _ _ _)
  · have dst : bytesAt s₁.mem (c.W + BitVec.ofNat 64 stO) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 stO) 16 :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide)
    rw [u₄.mem, u₃.mem, m₂, Proof.Cmac.xor2Mem_bytes _ (by
        rw [Offset.add_add]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
        (by rw [Offset.add_add]; exact L.w_w (.inr (by decide)) (by decide) (by decide)), b₁, dst]

/-! ## The loop -/

/-- One iteration of the loop, for the component `i < N`. -/
theorem aStep_wp {c : Cx} (L : Lay c) {σ s : State} {i : Nat} (h : AInv c σ i s) (hi : i < c.N) :
    WP isa (.seq (.block adNext) (.seq (cmacOf stO) (.block adStep))) s (AInv c σ (i + 1)) := by
  have aw := L.aw
  have hRb := L.rb
  refine WP.seq (WP.mono (adNext_wp L h hi) fun s₁ ⟨h19₁, h20₁, k₁⟩ => ?_)
  obtain E₁ := h.env.of_pk k₁.pk
  obtain hP : Buf c s₁ (descW σ.mem c.A i 0) (descW σ.mem c.A i 1).toNat := (h.ads i hi).of_eq k₁.pk.rd k₁.pk.wr
  refine WP.seq (WP.mono (cmacOf_wp L E₁ (st := stO) (by decide) (by decide) hP h19₁ (by rw [h20₁]; simp))
    fun s₂ ⟨K₂, f₂, out₂⟩ => ?_)
  obtain E₂ := E₁.of_pk K₂.pk
  obtain h17₂ : s₂.gpr .s4 = c.A + BitVec.ofNat 64 (16 * i) := by rw [K₂.s4, k₁.s4, h.s4]
  obtain h18₂ : s₂.gpr .s5 = BitVec.ofNat 64 (c.N - i) := by rw [K₂.s5, k₁.s5, h.s5]
  refine WP.mono (adStep_wp L E₂ (i := i) (k := c.N - i) (by omega_using [hi]) (by omega_using [aw]) h17₂ h18₂)
    fun s₃ ⟨pk₃, h17₃, h18₃, f₃, b₃⟩ => ?_
  -- The memory.
  obtain f₀₂ : Frame (wR c) σ.mem s₂.mem := h.frame.trans (by rw [← k₁.mem]; exact f₂.sub (macR_wR (by decide)
    (by decide)))
  obtain f₂₃ : Frame (wR c) s₂.mem s₃.mem := f₃.sub (w16_wR (.inl (by decide)) (by decide))
  obtain dc : ∀ r ∈ wR c, (⟨c.C, 512⟩ : Region).Disjoint r := dis_wR L.c_w
  obtain mac₁ : Spec.Siv.ctxMac s₁.mem c.C c.R = Spec.Siv.ctxMac σ.mem c.C c.R := by
    rw [k₁.mem]; exact ctxMac_frame h.frame dc hRb
  obtain comp₁ : bytesAt s₁.mem (descW σ.mem c.A i 0) (descW σ.mem c.A i 1).toNat =
      bytesAt σ.mem (descW σ.mem c.A i 0) (descW σ.mem c.A i 1).toNat := by
    rw [k₁.mem]; exact Proof.Cmac.bytesAt_frame h.frame (dis_wR (h.ads i hi).w) (by have := (h.ads i hi).lt; omega_using [])
  obtain dD₂ : bytesAt s₂.mem (c.W + BitVec.ofNat 64 dO) 16 = bytesAt s₁.mem (c.W + BitVec.ofNat 64 dO) 16 := by
    refine Proof.Cmac.bytesAt_frame f₂ (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  obtain hl := length_components σ.mem c.A c.N
  refine ⟨E₂.of_pk pk₃, (h.pk.trans k₁.pk).trans (K₂.pk.trans pk₃),
    h.ads.of_eq (by rw [pk₃.rd, K₂.pk.rd, k₁.pk.rd]) (by rw [pk₃.wr, K₂.pk.wr, k₁.pk.wr]), h17₃, ?_,
    f₀₂.trans f₂₃, ?_⟩
  · rw [h18₃, Nat.sub_sub]
  · rw [b₃, out₂, dD₂, mac₁, comp₁, k₁.mem, h.acc, List.take_succ_eq_append_getElem (by omega_using [hi, hl]),
      s2vAcc_snoc, components_getElem σ.mem c.A hi]
    rfl

/-- S2V over all the components, from S2V's first state in `D`. -/
theorem s2vAds_wp {c : Cx} (L : Lay c) {σ s : State} (h : AInv c σ 0 s) :
    WP isa s2vAds s (AInv c σ c.N) := by
  have aw := L.aw
  obtain hN : c.N < 2 ^ 64 := by omega_using [aw]
  obtain h18 : s.gpr .s5 = BitVec.ofNat 64 c.N := by rw [h.s5, Nat.sub_zero]
  unfold s2vAds
  refine WP.ite (decide (c.N = 0)) (eval_zero_ofNat _ _ hN h18) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.N = 0 := by simpa using ht
    exact WP.block_nil (by rw [h0]; exact h)
  · have h0 : c.N ≠ 0 := by simpa using hf
    refine WP.loop (M := isa) (fun (n : Nat) (t : State) => ∃ j, n = c.N - j ∧ j < c.N ∧ AInv c σ j t)
      ?_ (c.N - 0) s ⟨0, rfl, by omega_using [h0], h⟩
    rintro n t ⟨j, rfl, hj, hI⟩
    refine WP.mono (aStep_wp L hI hj) fun t' hI' => ?_
    obtain ev := eval_nonzero_ofNat _ _ (k := c.N - (j + 1)) (by omega_using [aw]) hI'.s5
    by_cases hz : c.N - (j + 1) = 0
    · left
      refine ⟨by rw [ev]; simp [hz], ?_⟩
      obtain e : j + 1 = c.N := by omega_using [hj, hz]
      rw [e] at hI'; exact hI'
    · right
      exact ⟨by rw [ev]; simp [hz], c.N - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hz], hI'⟩

end VG.Proof.AesSiv.RISCV64

end

end

/-!
# AES-SIV on RISC-V: finishing S2V with a string shorter than a block

Untrusted: everything here is checked by Lean. For a last string `P` of
`L < 16` bytes, `shortTail` zeroes the tail at `W + 32`, copies `P` into it
(AES-CCM's `copy`, a byte at a time) and puts `0x80` after it, so the tail
is `pad(P)`, doubles `D` into `W + 272` a byte at a time and XORs it into
the tail (`shortTail_wp`); `shortMac` computes the CMAC of the tail, one
complete block, into `W + out` (`shortMac_wp`), which is S2V's end
(`Siv.s2vFinish_short`, `short_wp`). As on PPC64LE
(`Proof/AesSiv/PPC64LE/Short.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64 VG.WriteBytes
open VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Proof.CmacAes.Stream.RISCV64 (FArgs)
open VG.Proof.AesCcm.RISCV64 (BytesPre copy_wp copyRegs)
open VG.Spec.Aes (bytesAt)

/-- What S2V's end writes: `wR` and its result at `W + out`. -/
abbrev oR (c : Cx) (out : Nat) : List Region := ⟨c.W + BitVec.ofNat 64 out, 16⟩ :: wR c

theorem copyRegs_keep : ∀ r ∈ keepRegs, r ∉ copyRegs := by decide

theorem PK.ofKeeps {s t : State} (h : VG.Proof.AesCcm.RISCV64.Keeps s t) : PK s t :=
  ⟨h.rd, h.wr, h.sp, fun r hr => h.gpr r (copyRegs_keep r hr)⟩

/-- The tail after the copy: `P` on zeros. -/
abbrev copiedMem (m : Mem) (W : Addr) (xs : List Byte) : Mem :=
  writeBytes (Proof.Cmac.zero2 m (W + BitVec.ofNat 64 tailO)) (W + BitVec.ofNat 64 tailO) xs

/-- `P` copied onto the zeroed tail (zeroed from `m₀`), if it is not empty. -/
theorem shortIte_wp {c : Cx} {s₁ : State} (E₁ : Env c s₁) {P : Addr} {n : Nat} (hP : Buf c s₁ P n)
    (hn : n < 16) (h19 : s₁.gpr .s6 = P) (h20₁ : s₁.gpr .s7 = BitVec.ofNat 64 n) {m₀ : Mem}
    (m₁ : s₁.mem = Proof.Cmac.zero2 m₀ (c.W + BitVec.ofNat 64 tailO)) (pmem : bytesAt s₁.mem P n = bytesAt m₀ P n) :
    WP isa (.ite (.zero .s7) (.block [])
        (.seq (.block [mov .a0 .s6, .addi .a1 .s1 (tailO : Int), mov .a2 .s7]) Impl.AesCcm.RISCV64.copy))
      s₁ fun s' => PK s₁ s' ∧ s'.gpr .s7 = s₁.gpr .s7 ∧
      s'.mem = copiedMem m₀ c.W (bytesAt m₀ P n) := by
  refine WP.ite (decide (n = 0)) (eval_zero_ofNat _ _ (by omega_using [hn]) h20₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨PK.refl _, rfl, ?_⟩
    rw [m₁]; simp [bytesAt, writeBytes_nil]
  · have h0 : n ≠ 0 := by simpa using hf
    obtain cw : Covers [⟨c.W + BitVec.ofNat 64 tailO, n⟩] s₁.wr :=
      VG.Proof.AesCcm.RISCV64.covers_prefix (E₁.perm.wC (d := tailO) (n := 16) (by decide)) (by omega_using [hn])
    obtain A : WP isa (.block [mov .a0 .s6, .addi .a1 .s1 (tailO : Int), mov .a2 .s7]) s₁ fun s₄ => PK s₁ s₄ ∧
        s₄.mem = s₁.mem ∧ s₄.gpr .s7 = s₁.gpr .s7 ∧ BytesPre s₄ P (c.W + BitVec.ofNat 64 tailO) n := by
      refine wp_mv fun s₂ u₂ => wp_addi (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ =>
        WP.block_nil ⟨(PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)),
          by rw [u₄.mem, u₃.mem, u₂.mem], by rw [u₄.other _ (by decide), u₃.other _ (by decide),
            u₂.other _ (by decide)], ?_⟩
      exact ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h19],
        by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), E₁.s1],
        by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h20₁], by omega_using [h0], by omega_using [hn],
        by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hP.rd,
        by rw [u₄.wr, u₃.wr, u₂.wr]; exact cw,
        (hP.wd (d := tailO) (k := 16) (by decide)).sub_right (Region.sub_prefix (by omega_using [hn]))⟩
    refine WP.seq (WP.mono A fun s₄ ⟨pk₄, m₄, r20₄, hb⟩ => WP.mono (copy_wp s₄ hb) fun s₅ ⟨m₅, _, k₅⟩ =>
      ⟨pk₄.trans (PK.ofKeeps k₅), by rw [k₅.gpr .s7 (by decide), r20₄], ?_⟩)
    rw [m₅, m₄, pmem, m₁]

/-- `0x80` after `P` (`n` bytes) in the tail, `dbl(D)` into `W + 272` and
the XOR of it into the tail. -/
theorem shortPad_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {n : Nat} (hn : n < 16)
    (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa (.block (([.add .t0 .s1 .s7, .li .t1 0x80, .store .b .t1 .t0 tailO] : List Instr) ++
      Impl.Cmac.RISCV64.dbl 16 0x87 dO dbO ++ xor16 tailO dbO tailO)) s fun s' => PK s s' ∧
      Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩, ⟨c.W + BitVec.ofNat 64 dbO, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 tailO) 16 =
        Spec.Cmac.xor (bytesAt (s.mem.writeW (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 n) (0x80 : Byte))
            (c.W + BitVec.ofNat 64 tailO) 16)
          (Spec.Cmac.dbl 16 (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16)) := by
  have ww := L.ww
  simp only [List.cons_append, List.nil_append]
  refine wp_add fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => ?_
  obtain a80 : s₂.gpr .t0 + BitVec.ofNat 64 tailO = c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 n := by
    rw [u₂.other _ (by decide), u₁.gpr, E.s1, h20, Offset.add_add, Offset.add_add, Nat.add_comm]
  refine wp_sb (by decide) a80 (by
      rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by simp only [tailO]; omega_using [hn])) fun s₃ u₃ => ?_
  obtain pk₃ : PK s s₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofMupd u₃))
  obtain E₃ := E.of_pk pk₃
  obtain b : (BitVec.setWidth 8 (BitVec.ofNat 64 128) : Byte) = 0x80 := by decide
  obtain m₃ : s₃.mem = s.mem.writeW (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 n) (0x80 : Byte) := by
    rw [u₃.mem, u₂.gpr, u₂.mem, u₁.mem, b]
  obtain fP : Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩] s.mem s₃.mem := by
    rw [m₃]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := n) (n := 8 / 8) (k := 16) (by omega_using [hn]) (by omega_using [hn]))
  refine Proof.Cmac.RISCV64.dbl_wp (K := c.W) (src := dO) (dst := dbO) (by decide) (by decide)
    Proof.Cmac.RISCV64.dbl_spec16 E₃.s1 (.inr (by decide)) (by decide) (by decide) (by simp only [dbO]; omega_using [ww])
    (fun j hj => E₃.perm.wR (by simp only [dO]; omega_using [hj])) (fun j hj => E₃.perm.wW (by simp only [dbO]; omega_using [hj]))
    fun s₄ g₄ rd₄ wr₄ sp₄ f₄ b₄ => ?_
  obtain pk₄ : PK s₃ s₄ := ⟨rd₄, wr₄, sp₄, fun r hr => g₄ r (fun e => by subst e; exact absurd hr (by decide))
    (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))
    (fun e => by subst e; exact absurd hr (by decide))⟩
  obtain E₄ := E₃.of_pk pk₄
  rw [← List.append_nil (xor16 tailO dbO tailO)]
  refine xor16_wp L E₄ (a := tailO) (b := dbO) (d := tailO) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun s₅ pk₅ g₅ m₅ => WP.block_nil ⟨pk₃.trans (pk₄.trans pk₅), ?_, ?_⟩
  · rw [m₅]
    exact ((fP.mono (by simp)).trans (f₄.mono (by simp))).trans ((Proof.Cmac.xor2Mem_frame _ _ _ _).mono (by simp))
  · have dTB : (⟨c.W + BitVec.ofNat 64 tailO, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 dbO, 16⟩ :=
      L.w_w (.inl (by decide)) (by decide) (by decide)
    obtain dD : (⟨c.W + BitVec.ofNat 64 dO, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 tailO, 16⟩ :=
      L.w_w (.inr (by decide)) (by decide) (by decide)
    rw [m₅, Proof.Cmac.xor2Mem_bytes _ (by
        rw [Offset.add_add]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
        (by rw [Offset.add_add]; exact L.w_w (.inl (by decide)) (by decide) (by decide)), b₄,
      Proof.Cmac.bytesAt_frame f₄ (p := c.W + BitVec.ofNat 64 tailO) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dTB) (by decide),
      Proof.Cmac.bytesAt_frame fP (p := c.W + BitVec.ofNat 64 dO) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dD) (by decide), m₃]

/-- The tail after `shortTail`: `pad(P) ⊕ dbl(D)`. -/
theorem shortTail_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (hn : n < 16) (h19 : s.gpr .s6 = P) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa shortTail s fun s' => PK s s' ∧
      Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩, ⟨c.W + BitVec.ofNat 64 dbO, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 tailO) 16 =
        Spec.Cmac.xor (Spec.Siv.pad (bytesAt s.mem P n)) (Spec.Siv.dbl (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16)) := by
  have ww := L.ww
  obtain hlen : (bytesAt s.mem P n).length = n := Proof.Cmac.bytesAt_length _ _ _
  unfold shortTail
  refine WP.seq (zero16_wp L E (d := tailO) (is := []) (by decide) (by decide) fun s₁ pk₁ g₁ m₁ =>
    WP.block_nil ?_)
  show WP isa _ s₁ _
  obtain E₁ := E.of_pk pk₁
  obtain pmem : bytesAt s₁.mem P n = bytesAt s.mem P n := by
    rw [m₁]
    exact Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.wd (by decide)) (by have := hP.lt; omega_using [hn])
  refine WP.seq (WP.mono (shortIte_wp E₁ (hP.of_eq pk₁.rd pk₁.wr) hn (by rw [g₁ _ (by decide), h19])
    (by rw [g₁ _ (by decide), h20]) m₁ pmem) fun s₂ ⟨pk₂, r20₂, m₂⟩ => ?_)
  obtain E₂ := E₁.of_pk pk₂
  refine WP.mono (shortPad_wp L E₂ (n := n) hn (by rw [r20₂, g₁ _ (by decide), h20]))
    fun s₃ ⟨pk₃, f₃, t₃⟩ => ⟨pk₁.trans (pk₂.trans pk₃), ?_, ?_⟩
  -- The memory.
  · have fC : Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩] s.mem s₂.mem := by
      rw [m₂]
      exact (Proof.Cmac.frame_store2 _ _ _).trans (writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base (c.W + BitVec.ofNat 64 tailO) (d := 0) (n := n) (k := 16)
          (by omega_using [hn]) (by decide)))
    exact (fC.mono (by simp)).trans f₃
  -- The tail.
  · have dD : (⟨c.W + BitVec.ofNat 64 dO, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 tailO, 16⟩ :=
      L.w_w (.inr (by decide)) (by decide) (by decide)
    obtain pad := Proof.Cmac.padded_bytes (Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 tailO))
      (c.W + BitVec.ofNat 64 tailO) (bytesAt s.mem P n) (by rw [hlen]; exact hn) (Proof.Cmac.zero2_bytes _ _)
    obtain fC : Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩] s.mem s₂.mem := by
      rw [m₂]
      exact (Proof.Cmac.frame_store2 _ _ _).trans (writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base (c.W + BitVec.ofNat 64 tailO) (d := 0) (n := n) (k := 16)
          (by omega_using [hn]) (by decide)))
    rw [hlen] at pad
    rw [t₃, Proof.Cmac.bytesAt_frame fC (p := c.W + BitVec.ofNat 64 dO) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dD) (by decide), m₂]
    simp only [copiedMem]
    rw [pad, Spec.Siv.pad, Spec.Siv.dbl, hlen, show 16 - n - 1 = 15 - n by omega_using []]
    rfl

/-- The CMAC of one block. -/
theorem macWith_one (ciph : Spec.Cmac.Cipher) (k1 k2 T : List Byte) (hT : T.length = 16) :
    Spec.Cmac.macWith ciph 16 k1 k2 T = ciph (Spec.Cmac.xor (Spec.Cmac.zeros 16) (Spec.Cmac.lastBlock 16 k1 k2 T)) := by
  rw [Siv.macWith_chained, hT, show Spec.Cmac.chainedLen 16 16 = 0 from rfl, List.take_zero, List.drop_zero]
  rfl

/-- `shortMac`: the CMAC of the tail, one complete block, into `W + out`. -/
theorem shortMac_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (shortMac out) s fun s' => PK s s' ∧
      Frame [⟨c.W + BitVec.ofNat 64 out, 16⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 out) 16 =
        Spec.Siv.ctxMac s.mem c.C c.R (bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) 16) := by
  have hRb := L.rb
  obtain ho : out + 16 ≤ tailO ∨ tailO + 16 ≤ out := by rcases hout with rfl | rfl <;> decide
  obtain ho' : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  obtain ho8 : out % 8 = 0 := by rcases hout with rfl | rfl <;> decide
  unfold shortMac shortArgs
  rw [List.append_assoc]
  refine WP.seq (zero16_wp L E (d := out) (by omega_using [ho']) ho8 fun s₁ pk₁ g₁ m₁ => ?_)
  obtain E₁ := E.of_pk pk₁
  unfold macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_using [ho']) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_addi (by decide) fun t₅ v₅ =>
    wp_li (by decide) fun t₆ v₆ => WP.block_nil ?_
  obtain pk₆ : PK s₁ t₆ := (PK.ofUpd v₁).trans ((PK.ofUpd v₂).trans ((PK.ofUpd v₃).trans ((PK.ofUpd v₄).trans
    ((PK.ofUpd v₅).trans (PK.ofUpd v₆)))))
  obtain E₆ := E₁.of_pk pk₆
  obtain F := fargs L E₆ (y := out) ho' (Nat.le_refl 16) (L.srcW E₆.perm (t := tailO) (k := 16) (by decide))
    (L.w_w (by omega_using [ho]) (by decide) (by omega_using [ho']))
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E₁.s2])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E₁.s3])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1])
    (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1])
    (by rw [v₆.gpr])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1]; rfl)
  obtain m₆ : t₆.mem = s₁.mem := by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  refine WP.mono (fin_call_raw F) fun s₂ h₂ => ⟨pk₁.trans (pk₆.trans (PK.ofSaved h₂.rd h₂.wr h₂.sp h₂.saved)),
    ?_, ?_⟩
  · have f₁ : Frame [⟨c.W + BitVec.ofNat 64 out, 16⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩] s.mem s₁.mem := by
      rw [m₁]; exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
    exact f₁.trans (by rw [← m₆]; exact h₂.frame)
  -- What the call reads.
  obtain dC : ∀ {d k : Nat}, d + k ≤ 512 → ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 out, 16⟩ : Region)],
      (⟨c.C + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.c_w' hd (by omega_using [ho'])
  obtain f₁ : Frame [⟨c.W + BitVec.ofNat 64 out, 16⟩] s.mem s₁.mem := by rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _
  have cK {d k : Nat} (hd : d + k ≤ 512) :
      bytesAt s₁.mem (c.C + BitVec.ofNat 64 d) k = bytesAt s.mem (c.C + BitVec.ofNat 64 d) k :=
    Proof.Cmac.bytesAt_frame f₁ (dC hd) (by omega_using [hd])
  obtain sch := cK (d := 0) (k := 16 * (c.R + 1)) (by omega_using [hRb])
  rw [BitVec.add_zero] at sch
  obtain tl : bytesAt s₁.mem (c.W + BitVec.ofNat 64 tailO) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) 16 :=
    Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_using [ho]) (by decide) (by omega_using [ho'])) (by decide)
  obtain z : bytesAt s₁.mem (c.W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero2_bytes]
  rw [h₂.out, m₆, Proof.CmacAes.RISCV64.mn, Proof.CmacAes.RISCV64.ciphAt, sch, cK (d := 240) (k := 16) (by decide),
    cK (d := 256) (k := 16) (by decide), tl, z, Spec.Siv.ctxMac, Spec.Siv.schedCiph,
    macWith_one _ _ _ _ (Proof.Cmac.bytesAt_length _ _ _)]
  rfl

/-- S2V's end for a string `P` shorter than a block, into `W + out`. -/
theorem short_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (hn : n < 16) (h19 : s.gpr .s6 = P) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) {out : Nat}
    (hout : out = 0 ∨ out = tO) :
    WP isa (.seq shortTail (shortMac out)) s fun s' => PK s s' ∧ Frame (oR c out) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem c.C c.R)
          (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16) (bytesAt s.mem P n) := by
  have hRb := L.rb
  refine WP.seq (WP.mono (shortTail_wp L E hP hn h19 h20) fun s₁ ⟨pk₁, f₁, t₁⟩ => ?_)
  refine WP.mono (shortMac_wp L (E.of_pk pk₁) hout) fun s₂ ⟨pk₂, f₂, o₂⟩ => ⟨pk₁.trans pk₂, ?_, ?_⟩
  · refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨c.W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · have dc : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 tailO, 16⟩ : Region), ⟨c.W + BitVec.ofNat 64 dbO, 16⟩],
        (⟨c.C, 512⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.c0_w' (by decide) (by decide)
      · exact L.c0_w' (by decide) (by decide)
    rw [o₂, t₁, ctxMac_frame f₁ dc hRb, Siv.s2vFinish_short _ _ (by rw [Proof.Cmac.bytesAt_length]; exact hn),
      Siv.xor_eq, Proof.Cmac.xor_comm]

end VG.Proof.AesSiv.RISCV64

end

end

/-!
# AES-SIV on RISC-V: finishing S2V with a string of a block or more

Untrusted: everything here is checked by Lean. For a last string `P` of
`L ≥ 16` bytes, `kBlock` computes `16 k` for the `k` blocks of `P` chained
before its tail (`AesSiv.kOf`), `tailCopy` copies the last `L − 16 k` bytes
(16 to 32) to the tail at `W + 32` (AES-CCM's `copy`) and XORs `D` into its
last 16, at any alignment, a byte at a time (AES-CCM's `xorBytes`;
`tailCopy_wp`, `xorend_writeBytes`); `longMac` chains the `k` blocks of
`P`, then the first `j` blocks of the tail (`AesSiv.jOf`), and finalizes
the rest, into `W + out` (`longMac_wp`), which is S2V's end
(`AesSiv.long_spec`). As on PPC64LE (`Proof/AesSiv/PPC64LE/Long.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64 VG.WriteBytes
open VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Proof.CmacAes.Stream.RISCV64 (UArgs upd_call FArgs)
open VG.Proof.AesCcm.RISCV64 (BytesPre copy_wp xorBytes_wp xorL)
open VG.Spec.Aes (bytesAt)

/-- `(L − 1) / 16` in `t0`. -/
theorem lenDiv_eq {s s₁ s₂ : State} {n : Nat} (hn : n < 2 ^ 64) (h1 : 1 ≤ n)
    (h20 : s.gpr .s7 = BitVec.ofNat 64 n)
    (u₁ : Upd s s₁ .t0 (s.gpr .s7 - BitVec.ofNat 64 1)) (u₂ : Upd s₁ s₂ .t0 (s₁.gpr .t0 >>> 4)) :
    s₂.gpr .t0 = BitVec.ofNat 64 ((n - 1) / 16) := by
  rw [u₂.gpr, u₁.gpr, h20, ofNat_sub' h1 hn, ofNat_lsr4' (by omega_using [hn])]

/-- `kBlock`: `16 k` in `s8`. -/
theorem kBlock_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h16 : 16 ≤ n) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa kBlock s fun s' => MacKeep s s' ∧ s'.mem = s.mem ∧ s'.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) := by
  unfold kBlock
  refine WP.seq (wp_subi (imm := 1) (by decide) fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ =>
    wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
  obtain K₃ : MacKeep s s₃ := (MacKeep.ofUpd u₁).trans ((MacKeep.ofUpd u₂).trans (MacKeep.ofUpd u₃))
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain h9 : s₃.gpr .t0 = BitVec.ofNat 64 ((n - 1) / 16) := by
    rw [u₃.other _ (by decide)]; exact lenDiv_eq hn (by omega_using [h16]) h20 u₁ u₂
  refine WP.ite (decide ((n - 1) / 16 = 0)) (eval_zero_ofNat _ _ (by omega_using [hn]) h9) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : (n - 1) / 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨K₃, m₃, by rw [u₃.gpr, kOf_lt (by omega_using [h0])]⟩
  · have h0 : (n - 1) / 16 ≠ 0 := by simpa using hf
    refine wp_subi (imm := 1) (by decide) fun s₄ u₄ => wp_sll (by decide) fun s₅ u₅ =>
      WP.block_nil ⟨K₃.trans ((MacKeep.ofUpd u₄).trans (MacKeep.ofUpd u₅)), by rw [u₅.mem, u₄.mem, m₃], ?_⟩
    rw [u₅.gpr, u₄.gpr, h9, ofNat_sub' (by omega_using [h0]) (by omega_using [hn]), ofNat_shl4 (by omega_using [hn]), kOf_ge (by omega_using [h0])]

/-- `jBlock`: `j` in `s0`. -/
theorem jBlock_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h16 : 16 ≤ n) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa jBlock s fun s' => MacKeep s s' ∧ s'.mem = s.mem ∧ s'.gpr .s8 = s.gpr .s8 ∧
      s'.gpr .s0 = BitVec.ofNat 64 (jOf n) := by
  unfold jBlock
  refine WP.seq (wp_subi (imm := 1) (by decide) fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ =>
    wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
  obtain K₃ : MacKeep s s₃ := (MacKeep.ofUpd u₁).trans ((MacKeep.ofUpd u₂).trans (MacKeep.ofUpd u₃))
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain r21₃ : s₃.gpr .s8 = s.gpr .s8 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain h9 : s₃.gpr .t0 = BitVec.ofNat 64 ((n - 1) / 16) := by
    rw [u₃.other _ (by decide)]; exact lenDiv_eq hn (by omega_using [h16]) h20 u₁ u₂
  refine WP.ite (decide ((n - 1) / 16 = 0)) (eval_zero_ofNat _ _ (by omega_using [hn]) h9) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : (n - 1) / 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨K₃, m₃, r21₃, by rw [u₃.gpr, show jOf n = 0 by unfold jOf; split <;> omega_arith]⟩
  · have h0 : (n - 1) / 16 ≠ 0 := by simpa using hf
    refine wp_li (by decide) fun s₄ u₄ => WP.block_nil ⟨K₃.trans (MacKeep.ofUpd u₄), by rw [u₄.mem, m₃],
      by rw [u₄.other _ (by decide), r21₃], ?_⟩
    rw [u₄.gpr, show jOf n = 1 by unfold jOf; split <;> omega_arith]

/-- The last 16 of `T ≥ 16` bytes at `B`, XORed with the 16 at `Q`, a byte
at a time: `xorend` of the bytes at `B` and those at `Q`. -/
theorem xorend_writeBytes (m : Mem) {B Q : Addr} {T : Nat} (hT : 16 ≤ T) (hw : B.toNat + T ≤ 2 ^ 64) :
    bytesAt (writeBytes m (B + BitVec.ofNat 64 (T - 16))
        (xorL (bytesAt m (B + BitVec.ofNat 64 (T - 16)) 16) (bytesAt m Q 16))) B T =
      Spec.Siv.xorend (bytesAt m B T) (bytesAt m Q 16) := by
  obtain e : T = (T - 16) + 16 := by omega_using [hT]
  obtain hx : (xorL (bytesAt m (B + BitVec.ofNat 64 (T - 16)) 16) (bytesAt m Q 16)).length = 16 := by
    simp [Proof.Cmac.bytesAt_length]
  obtain hs := Proof.Cmac.Stream.bytesAt_append (writeBytes m (B + BitVec.ofNat 64 (T - 16))
    (xorL (bytesAt m (B + BitVec.ofNat 64 (T - 16)) 16) (bytesAt m Q 16))) B (T - 16) 16
  rw [← e] at hs
  rw [hs, Spec.Siv.xorend, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
  obtain tk := take_bytesAt m B (a := T - 16) (b := 16)
  obtain dr := drop_bytesAt m B (a := T - 16) (b := 16)
  rw [← e] at tk dr
  rw [tk, dr, Proof.Cmac.bytesAt_frame (writeBytes_frame _ _ _ (R := ⟨B + BitVec.ofNat 64 (T - 16), 16⟩)
      (by rw [hx]; exact Region.contains_self _ _)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint B (by omega_using []) (by omega_using [hw])) (by omega_using [hw]),
    Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [hx]) (by decide), hx,
    List.drop_eq_nil_of_le (by rw [Proof.Cmac.bytesAt_length]), List.append_nil]
  rfl

/-- `tailCopy`: the last `T = L − 16 k` bytes of `P` copied to the tail,
with `D` XORed into their last 16. -/
theorem tailCopy_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n k : Nat} (hP : Buf c s P n)
    (hk : 16 * k ≤ n) (hT : 16 ≤ n - 16 * k) (hT' : n - 16 * k ≤ 32) (h19 : s.gpr .s6 = P)
    (h20 : s.gpr .s7 = BitVec.ofNat 64 n) (h21 : s.gpr .s8 = BitVec.ofNat 64 (16 * k)) :
    WP isa tailCopy s fun s' => MacKeep s s' ∧ s'.gpr .s8 = s.gpr .s8 ∧
      Frame [⟨c.W + BitVec.ofNat 64 tailO, 32⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 tailO) (n - 16 * k) =
        Spec.Siv.xorend (bytesAt s.mem (P + BitVec.ofNat 64 (16 * k)) (n - 16 * k))
          (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16) := by
  have hn := hP.lt
  have ww := L.ww
  obtain hQ := hP.drop hk
  unfold tailCopy
  obtain A : WP isa (.block [.add .a0 .s6 .s8, .addi .a1 .s1 (tailO : Int), .sub .a2 .s7 .s8]) s fun s₃ =>
      MacKeep s s₃ ∧ s₃.mem = s.mem ∧ s₃.gpr .s8 = s.gpr .s8 ∧
      BytesPre s₃ (P + BitVec.ofNat 64 (16 * k)) (c.W + BitVec.ofNat 64 tailO) (n - 16 * k) := by
    refine wp_add fun s₁ u₁ => wp_addi (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ =>
      WP.block_nil ⟨(MacKeep.ofUpd u₁).trans ((MacKeep.ofUpd u₂).trans (MacKeep.ofUpd u₃)),
        by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide)], ?_⟩
    obtain rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
    obtain wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
    obtain cw : Covers [⟨c.W + BitVec.ofNat 64 tailO, n - 16 * k⟩] s.wr :=
      VG.Proof.AesCcm.RISCV64.covers_prefix (E.perm.wC (d := tailO) (n := 32) (by decide)) hT'
    exact ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h19, h21],
      by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s1],
      by simp (disch := decide) only [u₃.gpr, u₂.other, u₁.other, h20, h21]; exact ofNat_sub' hk hn,
      by omega_using [hT], by omega_using [hT'], by rw [rd₃, wr₃]; exact hQ.rd, by rw [wr₃]; exact cw,
      (hQ.wd (d := tailO) (k := 32) (by decide)).sub_right (Region.sub_prefix hT')⟩
  refine WP.seq (WP.mono A fun s₃ ⟨K₃, m₃, r21₃, hb⟩ => WP.seq (WP.mono (copy_wp s₃ hb)
    fun s₄ ⟨m₄, _, k₄⟩ => ?_))
  obtain K₄ : MacKeep s₃ s₄ := ⟨PK.ofKeeps k₄, k₄.gpr _ (by decide), k₄.gpr _ (by decide), k₄.gpr _ (by decide),
    k₄.gpr _ (by decide)⟩
  obtain K₁₄ := K₃.trans K₄
  obtain E₄ := E.of_pk K₁₄.pk
  obtain r21₄ : s₄.gpr .s8 = s.gpr .s8 := by rw [k₄.gpr _ (by decide), r21₃]
  obtain r20₄ : s₄.gpr .s7 = BitVec.ofNat 64 n := by rw [K₁₄.s7, h20]
  -- `xorBytes`' arguments: `D`, and the tail's last 16 bytes.
  obtain eT : c.W + BitVec.ofNat 64 (n - 16 * k) + BitVec.ofNat 64 16 =
      c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 (n - 16 * k - 16) := by
    rw [Offset.add_add, Offset.add_add]; congr 2; simp only [tailO]; omega_using [hT]
  obtain B : WP isa (.block xorDArgs) s₄ fun s₉ => MacKeep s₄ s₉ ∧ s₉.mem = s₄.mem ∧ s₉.gpr .s8 = s₄.gpr .s8 ∧
      BytesPre s₉ (c.W + BitVec.ofNat 64 dO) (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 (n - 16 * k - 16))
        16 := by
    unfold xorDArgs
    refine wp_addi (by decide) fun s₅ u₅ => wp_sub fun s₆ u₆ => wp_add fun s₇ u₇ =>
      wp_addi (by decide) fun s₈ u₈ => wp_li (by decide) fun s₉ u₉ =>
      WP.block_nil ⟨(MacKeep.ofUpd u₅).trans ((MacKeep.ofUpd u₆).trans ((MacKeep.ofUpd u₇).trans
        ((MacKeep.ofUpd u₈).trans (MacKeep.ofUpd u₉)))), by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem],
        by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide)], ?_⟩
    obtain rd₉ : s₉.rd = s₄.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd]
    obtain wr₉ : s₉.wr = s₄.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr]
    obtain hsub : s₄.gpr .s7 - s₄.gpr .s8 = BitVec.ofNat 64 (n - 16 * k) := by
      rw [r20₄, r21₄, h21, ofNat_sub' hk hn]
    refine ⟨by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.gpr, E₄.s1],
      by
        simp (disch := decide) only [u₉.other, u₈.gpr, u₇.gpr, u₆.gpr, u₆.other, u₅.other]
        rw [E₄.s1, hsub, eT],
      by rw [u₉.gpr], by decide, by decide, by rw [rd₉, wr₉]; exact E₄.perm.wCR (by decide), ?_, ?_⟩
    · rw [wr₉, Offset.add_add]
      exact E₄.perm.wC (by simp only [tailO]; omega_using [hT'])
    · rw [Offset.add_add]
      exact L.w_w (.inr (by simp only [tailO, dO]; omega_using [hT'])) (by decide) (by simp only [tailO]; omega_using [hT'])
  refine WP.seq (WP.mono B fun s₉ ⟨K₉, m₉, r21₉, hb'⟩ => WP.mono (xorBytes_wp s₉ hb') fun s₁₀ ⟨m₁₀, _, k₁₀⟩ => ?_)
  obtain K₁₀ : MacKeep s₉ s₁₀ := ⟨PK.ofKeeps k₁₀, k₁₀.gpr _ (by decide), k₁₀.gpr _ (by decide),
    k₁₀.gpr _ (by decide), k₁₀.gpr _ (by decide)⟩
  obtain hlen : (bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * k)) (n - 16 * k)).length = n - 16 * k :=
    Proof.Cmac.bytesAt_length _ _ _
  obtain fW : Frame [⟨c.W + BitVec.ofNat 64 tailO, 32⟩] s.mem s₄.mem := by
    rw [m₄, m₃]
    exact writeBytes_frame _ _ _ (by
      rw [m₃] at hlen; rw [hlen]
      simpa using Offset.contains_base (c.W + BitVec.ofNat 64 tailO) (d := 0) (n := n - 16 * k) (k := 32)
        (by omega_using [hT']) (by decide))
  obtain hx : ∀ m : Mem, (xorL (bytesAt m (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 (n - 16 * k - 16)) 16)
      (bytesAt m (c.W + BitVec.ofNat 64 dO) 16)).length = 16 := fun m => by simp [Proof.Cmac.bytesAt_length]
  refine ⟨K₁₄.trans (K₉.trans K₁₀), by rw [k₁₀.gpr _ (by decide), r21₉, r21₄], ?_, ?_⟩
  -- The memory.
  · rw [m₁₀, m₉]
    exact fW.trans (writeBytes_frame _ _ _ (by
      rw [hx]
      exact Offset.contains_base _ (d := n - 16 * k - 16) (n := 16) (k := 32) (by omega_using [hT']) (by omega_using [hT'])))
  -- The tail.
  · have dT : (⟨c.W + BitVec.ofNat 64 tailO, 32⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 dO, 16⟩ :=
      L.w_w (.inl (by decide)) (by decide) (by decide)
    rw [m₁₀, m₉, xorend_writeBytes _ hT (by rw [L.wrapW (by decide)]; simp only [tailO]; omega_using [hT', ww]),
      Proof.Cmac.bytesAt_frame fW (p := c.W + BitVec.ofNat 64 dO) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dT.symm) (by decide), m₄,
      Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [hlen]) (by omega_using [hT']), hlen,
      List.drop_eq_nil_of_le (by rw [Proof.Cmac.bytesAt_length]), List.append_nil, m₃]

/-- The state at `W + out` is clear of the tail. -/
theorem out_tail {c : Cx} (L : Lay c) {out a k : Nat} (hout : out = 0 ∨ out = tO) (ha : 32 ≤ a) (hk : a + k ≤ 64) :
    (⟨c.W + BitVec.ofNat 64 a, k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 out, 16⟩ := by
  rcases hout with rfl | rfl
  · exact L.w_w (.inr (by omega_using [ha])) (by omega_using [hk]) (by decide)
  · exact L.w_w (.inl (by simp only [tO]; omega_using [hk])) (by omega_using [hk]) (by decide)

/-- `longMac`: the CMAC of the `k` blocks of `P` and the tail, into
`W + out`. -/
theorem longMac_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (h16 : 16 ≤ n) (h19 : s.gpr .s6 = P) (h20 : s.gpr .s7 = BitVec.ofNat 64 n)
    (h21 : s.gpr .s8 = BitVec.ofNat 64 (16 * kOf n)) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (longMac out) s fun s' => PK s s' ∧ Frame (macR c out) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 out) 16 =
        Spec.Siv.schedCiph s.mem c.C c.R (Spec.Cmac.xor
          (Spec.Cmac.lastBlock 16 (bytesAt s.mem (c.C + BitVec.ofNat 64 240) 16)
            (bytesAt s.mem (c.C + BitVec.ofNat 64 256) 16)
            ((bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) (n - 16 * kOf n)).drop (16 * jOf n)))
          (Spec.Cmac.chain (Spec.Siv.schedCiph s.mem c.C c.R)
            (Spec.Cmac.chain (Spec.Siv.schedCiph s.mem c.C c.R) (Spec.Cmac.zeros 16)
              (Spec.Cmac.blocks 16 (bytesAt s.mem P (16 * kOf n))))
            (Spec.Cmac.blocks 16 ((bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) (n - 16 * kOf n)).take
              (16 * jOf n))))) := by
  have hn := hP.lt
  have hRb := L.rb
  obtain hT := kOf_tail h16
  obtain hJ := jOf_rest h16
  obtain hj1 := jOf_le n
  obtain ho : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  obtain ho8 : out % 8 = 0 := by rcases hout with rfl | rfl <;> decide
  obtain hk : 16 * kOf n ≤ n := by omega_using [hT]
  generalize kOf n = k at hT hJ hk h21 ⊢
  -- The update over the `k` blocks of `P`.
  obtain A₁ : WP isa (.block (longArgs₁ out)) s fun s₁ => MacKeep s s₁ ∧ s₁.gpr .s8 = s.gpr .s8 ∧
      s₁.mem = Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 out) ∧
      UArgs s₁ c.C (c.W + BitVec.ofNat 64 out) P (c.W + BitVec.ofNat 64 384) c.R k := by
    unfold longArgs₁
    rw [List.append_assoc]
    refine zero16_wp L E (d := out) (by omega_using [ho]) ho8 fun s₀ pk₀ g₀ m₀ => ?_
    unfold macArgs
    simp only [List.cons_append, List.nil_append]
    refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_using [ho]) fun t₃ v₃ =>
      wp_addi (by decide) fun t₄ v₄ => wp_mv fun t₅ v₅ => wp_srl (by decide) fun t₆ v₆ =>
      WP.block_nil ?_
    obtain K₀ : MacKeep s s₀ := ⟨pk₀, g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide)⟩
    obtain K : MacKeep s₀ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
      ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
    obtain E₀ := E.of_pk pk₀
    obtain E₆ := E₀.of_pk K.pk
    obtain hq := (hP.take hk).of_eq (by rw [K.pk.rd, pk₀.rd]) (by rw [K.pk.wr, pk₀.wr])
    obtain r21₆ : t₆.gpr .s8 = s.gpr .s8 := by
      simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, g₀]
    refine ⟨K₀.trans K, r21₆, by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, m₀], ?_⟩
    exact uargs L E₆ ho hq.src (hq.wd (d := out) (k := 16) (by omega_using [ho])) (by omega_using [hn, hT])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.gpr, E₀.s2])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.gpr, v₁.other _ (by decide), E₀.s3])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
        v₂.other _ (by decide), v₁.other _ (by decide), E₀.s1])
      (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), g₀ _ (by decide), h19])
      (by
        simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, g₀, h21]
        rw [ofNat_lsr4' (by omega_using [hn, hT]), show 16 * k / 16 = k by omega_using []])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), E₀.s1]; rfl)
  unfold longMac
  refine WP.seq (WP.mono A₁ fun s₁ ⟨K₁, r21₁, m₁, U₁⟩ => ?_)
  refine WP.seq (WP.mono (upd_call U₁) fun s₂ h₂ => ?_)
  obtain K₂ : MacKeep s₁ s₂ := MacKeep.ofSaved h₂.rd h₂.wr h₂.sp h₂.saved
  obtain r21₂ : s₂.gpr .s8 = s.gpr .s8 := by rw [h₂.saved _ (by decide), r21₁]
  obtain K₁₂ := K₁.trans K₂
  refine WP.seq (WP.mono (jBlock_wp (s := s₂) hn h16 (by rw [K₁₂.s7, h20])) fun s₃ ⟨K₃, m₃, r21₃, r25₃⟩ => ?_)
  obtain K₁₃ := K₁₂.trans K₃
  obtain E₃ := E.of_pk K₁₃.pk
  obtain r21₃' : s₃.gpr .s8 = BitVec.ofNat 64 (16 * k) := by rw [r21₃, r21₂, h21]
  -- The update over the first `j` blocks of the tail.
  obtain A₂ : WP isa (.block (longArgs₂ out)) s₃ fun s₄ => MacKeep s₃ s₄ ∧ s₄.mem = s₃.mem ∧
      s₄.gpr .s8 = s₃.gpr .s8 ∧ s₄.gpr .s0 = s₃.gpr .s0 ∧
      UArgs s₄ c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 384) c.R
        (jOf n) := by
    unfold longArgs₂ macArgs
    simp only [List.cons_append, List.nil_append]
    refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_using [ho]) fun t₃ v₃ =>
      wp_addi (by decide) fun t₄ v₄ => wp_addi (by decide) fun t₅ v₅ =>
      wp_mv fun t₆ v₆ => WP.block_nil ?_
    obtain K : MacKeep s₃ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
      ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
    obtain E₆ := E₃.of_pk K.pk
    refine ⟨K, by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem],
      by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other],
      by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other], ?_⟩
    exact uargs L E₆ ho (L.srcW E₆.perm (t := tailO) (k := 16 * jOf n) (by simp only [tailO]; omega_using [hj1]))
      (out_tail L hout (by decide) (by simp only [tailO]; omega_using [hj1])) (by omega_using [hj1])
      (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.gpr, E₃.s2])
      (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.gpr, v₁.other, E₃.s3])
      (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.gpr, v₂.other, v₁.other, E₃.s1])
      (by simp (disch := decide) only [v₆.other, v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, E₃.s1])
      (by simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, r25₃])
      (by simp (disch := decide) only [v₆.other, v₅.other, v₄.gpr, v₃.other, v₂.other, v₁.other, E₃.s1]; rfl)
  refine WP.seq (WP.mono A₂ fun s₄ ⟨K₄, m₄, r21₄, r25₄, U₂⟩ => ?_)
  refine WP.seq (WP.mono (upd_call U₂) fun s₅ h₅ => ?_)
  obtain K₅ : MacKeep s₄ s₅ := MacKeep.ofSaved h₅.rd h₅.wr h₅.sp h₅.saved
  obtain K₁₅ := K₁₃.trans (K₄.trans K₅)
  obtain E₅ := E.of_pk K₁₅.pk
  obtain r21₅ : s₅.gpr .s8 = BitVec.ofNat 64 (16 * k) := by rw [h₅.saved _ (by decide), r21₄, r21₃']
  obtain r25₅ : s₅.gpr .s0 = BitVec.ofNat 64 (jOf n) := by rw [h₅.saved _ (by decide), r25₄, r25₃]
  obtain r20₅ : s₅.gpr .s7 = BitVec.ofNat 64 n := by rw [K₁₅.s7, h20]
  -- The finalization of the rest of the tail.
  obtain A₃ : WP isa (.block (longArgs₃ out)) s₅ fun s₆ => MacKeep s₅ s₆ ∧ s₆.mem = s₅.mem ∧
      FArgs s₆ c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 (tailO + 16 * jOf n))
        (c.W + BitVec.ofNat 64 384) (n - 16 * k - 16 * jOf n) c.R := by
    unfold longArgs₃ macArgs
    simp only [List.cons_append, List.nil_append]
    refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_using [ho]) fun t₃ v₃ =>
      wp_addi (by decide) fun t₄ v₄ => wp_addi (by decide) fun t₅ v₅ =>
      wp_sll (by decide) fun t₆ v₆ => wp_add fun t₇ v₇ => wp_sub fun t₈ v₈ => wp_sub fun t₉ v₉ =>
      WP.block_nil ?_
    obtain K : MacKeep s₅ t₉ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
      ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans ((MacKeep.ofUpd v₆).trans ((MacKeep.ofUpd v₇).trans
        ((MacKeep.ofUpd v₈).trans (MacKeep.ofUpd v₉))))))))
    obtain E₉ := E₅.of_pk K.pk
    obtain sh : t₆.gpr .t0 = BitVec.ofNat 64 (16 * jOf n) := by
      simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, r25₅]
      exact ofNat_shl4 (by omega_using [hj1])
    refine ⟨K, by rw [v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem], ?_⟩
    exact fargs L E₉ ho hJ.2.2 (L.srcW E₉.perm (t := tailO + 16 * jOf n) (k := n - 16 * k - 16 * jOf n)
        (by simp only [tailO]; omega_using [hj1, hT]))
      (out_tail L hout (by simp only [tailO]; omega_using []) (by simp only [tailO]; omega_using [hj1, hT]))
      (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other,
        v₂.other, v₁.gpr, E₅.s2])
      (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other,
        v₂.gpr, v₁.other, E₅.s3])
      (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.gpr,
        v₂.other, v₁.other, E₅.s1])
      (by
        simp (disch := decide) only [v₉.other, v₈.other, v₇.gpr, v₆.other, sh]
        simp (disch := decide) only [v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, E₅.s1]
        exact Offset.add_add _ _ _)
      (by
        simp (disch := decide) only [v₉.gpr, v₈.gpr, v₈.other, v₇.other, sh]
        simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, r20₅, r21₅]
        rw [ofNat_sub' hk hn, ofNat_sub' (by omega_using [hj1, hT]) (by omega_using [hn])])
      (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.gpr, v₃.other,
        v₂.other, v₁.other, E₅.s1]; rfl)
  refine WP.seq (WP.mono A₃ fun s₆ ⟨K₆, m₆, F⟩ => ?_)
  refine WP.mono (fin_call_raw F) fun s₇ h₇ => ?_
  obtain K₇ : MacKeep s₆ s₇ := MacKeep.ofSaved h₇.rd h₇.wr h₇.sp h₇.saved
  -- What each step writes.
  obtain f₁ : Frame (macR c out) s.mem s₁.mem := by
    rw [m₁]; exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
  obtain f₄ : Frame (macR c out) s.mem s₄.mem := f₁.trans (by rw [m₄, m₃]; exact h₂.frame)
  obtain f₆ : Frame (macR c out) s.mem s₆.mem := f₄.trans (by rw [m₆]; exact h₅.frame)
  refine ⟨(K₁₅.trans (K₆.trans K₇)).pk, f₆.trans h₇.frame, ?_⟩
  -- What the calls read is as on entry.
  obtain dc : ∀ r ∈ macR c out, (⟨c.C, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.c0_w' (by decide) (by omega_using [ho])
    · exact L.c0_w' (by decide) (by decide)
  obtain dt : ∀ r ∈ macR c out, (⟨c.W + BitVec.ofNat 64 tailO, 32⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact out_tail L hout (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have cK {d k : Nat} (hd : d + k ≤ 512) {m' : Mem} (hf : Frame (macR c out) s.mem m') :
      bytesAt m' (c.C + BitVec.ofNat 64 d) k = bytesAt s.mem (c.C + BitVec.ofNat 64 d) k :=
    Proof.Cmac.bytesAt_frame hf (fun r hr => (dc r hr).sub_left (Lay.cSub hd)) (by omega_using [hd])
  have cT {d k : Nat} (hd : d + k ≤ 32) {m' : Mem} (hf : Frame (macR c out) s.mem m') :
      bytesAt m' (c.W + BitVec.ofNat 64 (tailO + d)) k = bytesAt s.mem (c.W + BitVec.ofNat 64 (tailO + d)) k :=
    Proof.Cmac.bytesAt_frame hf (fun r hr => (dt r hr).sub_left (by
      rw [← Offset.add_add]; exact Offset.sub_base _ hd)) (by omega_using [hd])
  obtain k0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  obtain f₂ : Frame (macR c out) s.mem s₂.mem := by rw [← m₃, ← m₄]; exact f₄
  obtain f₅ : Frame (macR c out) s.mem s₅.mem := by rw [← m₆]; exact f₆
  obtain sch₁ := cK (d := 0) (k := 16 * (c.R + 1)) (by omega_using [hRb]) f₁
  obtain sch₄ := cK (d := 0) (k := 16 * (c.R + 1)) (by omega_using [hRb]) f₂
  obtain sch₆ := cK (d := 0) (k := 16 * (c.R + 1)) (by omega_using [hRb]) f₅
  obtain k1 := cK (d := 240) (k := 16) (by decide) f₅
  obtain k2 := cK (d := 256) (k := 16) (by decide) f₅
  obtain tl₄ := cT (d := 0) (k := 16 * jOf n) (by omega_using [hj1]) f₂
  obtain tl₆ := cT (d := 16 * jOf n) (k := n - 16 * k - 16 * jOf n) (by omega_using [hj1, hT]) f₅
  obtain pre₁ : bytesAt s₁.mem P (16 * k) = bytesAt s.mem P (16 * k) :=
    Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hP.take hk).wd (by omega_using [ho])
      · exact (hP.take hk).wd (by decide)) (by omega_using [hn, hT])
  rw [k0] at sch₁ sch₄ sch₆
  rw [Nat.add_zero] at tl₄
  obtain hz : bytesAt s₁.mem (c.W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero2_bytes]
  obtain hsplit : n - 16 * k = 16 * jOf n + (n - 16 * k - 16 * jOf n) := by omega_using [hj1, hT]
  obtain tk : (bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) (n - 16 * k)).take (16 * jOf n) =
      bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) (16 * jOf n) := by
    rw [hsplit, take_bytesAt]
  obtain dr : (bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) (n - 16 * k)).drop (16 * jOf n) =
      bytesAt s.mem (c.W + BitVec.ofNat 64 (tailO + 16 * jOf n)) (n - 16 * k - 16 * jOf n) := by
    rw [hsplit, drop_bytesAt, Offset.add_add, ← hsplit]
  have out₂ := h₂.out
  have out₅ := h₅.out
  have out₇ := h₇.out
  rw [m₆] at out₇
  rw [m₄, m₃] at out₅
  rw [out₇, out₅, out₂, Proof.CmacAes.RISCV64.mn, Proof.CmacAes.RISCV64.ciphAt, sch₆, k1, k2, tl₆,
    sch₄, Proof.Cmac.Stream.blocksAt_eq s₂.mem, tl₄, sch₁, hz, Proof.Cmac.Stream.blocksAt_eq s₁.mem, pre₁, tk, dr,
    Proof.Cmac.xor_comm]
  rfl

/-- S2V's end for a string `P` of a block or more, into `W + out`. -/
theorem long_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (h16 : 16 ≤ n) (h19 : s.gpr .s6 = P) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) {out : Nat}
    (hout : out = 0 ∨ out = tO) :
    WP isa (.seq longTail (longMac out)) s fun s' => PK s s' ∧ Frame (oR c out) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem c.C c.R)
          (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16) (bytesAt s.mem P n) := by
  have hn := hP.lt
  have hRb := L.rb
  obtain hT := kOf_tail h16
  unfold longTail
  refine WP.seq (WP.seq (WP.mono (kBlock_wp hn h16 h20) fun s₁ ⟨K₁, m₁, r21₁⟩ => ?_))
  obtain hk : 16 * kOf n ≤ n := by omega_using [hT]
  refine WP.mono (tailCopy_wp L (E.of_pk K₁.pk) (hP.of_eq K₁.pk.rd K₁.pk.wr) hk hT.1 hT.2
    (by rw [K₁.s6, h19]) (by rw [K₁.s7, h20]) r21₁) fun s₂ ⟨K₂, r21₂, f₂, t₂⟩ => ?_
  obtain K₁₂ := K₁.trans K₂
  refine WP.mono (longMac_wp L (E.of_pk K₁₂.pk) (hP.of_eq K₁₂.pk.rd K₁₂.pk.wr) h16 (by rw [K₁₂.s6, h19])
    (by rw [K₁₂.s7, h20]) (by rw [r21₂, r21₁]) hout) fun s₃ ⟨pk₃, f₃, o₃⟩ => ⟨K₁₂.pk.trans pk₃, ?_, ?_⟩
  -- What it writes.
  · have f₁₂ : Frame (oR c out) s.mem s₂.mem := by
      rw [← m₁]
      refine f₂.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    refine f₁₂.trans (f₃.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  -- The result.
  · rw [m₁] at f₂ t₂
    obtain dt : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 tailO, 32⟩ : Region)], (⟨c.C, 512⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact L.c0_w' (by decide) (by decide)
    have cK {d k : Nat} (hd : d + k ≤ 512) :
        bytesAt s₂.mem (c.C + BitVec.ofNat 64 d) k = bytesAt s.mem (c.C + BitVec.ofNat 64 d) k :=
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => (dt r hr).sub_left (Lay.cSub hd)) (by omega_using [hd])
    obtain sch := cK (d := 0) (k := 16 * (c.R + 1)) (by omega_using [hRb])
    rw [BitVec.add_zero] at sch
    obtain pre : bytesAt s₂.mem P (16 * kOf n) = bytesAt s.mem P (16 * kOf n) :=
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hP.take hk).wd (by decide)) (by omega_using [hn, hT])
    obtain hp : (bytesAt s.mem P n).length = n := Proof.Cmac.bytesAt_length _ _ _
    obtain hsplit : n = 16 * kOf n + (n - 16 * kOf n) := by omega_using [hT]
    obtain tk : (bytesAt s.mem P n).take (16 * kOf n) = bytesAt s.mem P (16 * kOf n) := by
      have := take_bytesAt s.mem P (a := 16 * kOf n) (b := n - 16 * kOf n)
      rwa [← hsplit] at this
    obtain dr : (bytesAt s.mem P n).drop (16 * kOf n) =
        bytesAt s.mem (P + BitVec.ofNat 64 (16 * kOf n)) (n - 16 * kOf n) := by
      have := drop_bytesAt s.mem P (a := 16 * kOf n) (b := n - 16 * kOf n)
      rwa [← hsplit] at this
    rw [o₃, Spec.Siv.schedCiph, sch, cK (d := 240) (k := 16) (by decide), cK (d := 256) (k := 16) (by decide),
      pre, t₂, Spec.Siv.ctxMac,
      ← long_spec _ _ _ _ _ (Proof.Cmac.bytesAt_length _ _ _) (by rw [hp]; exact h16), hp, tk, dr]
    rfl

/-- S2V's end, into `W + out`. -/
theorem finish_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (h19 : s.gpr .s6 = P) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (finish out) s fun s' => PK s s' ∧ Frame (oR c out) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem c.C c.R)
          (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16) (bytesAt s.mem P n) := by
  have hn := hP.lt
  unfold finish
  refine WP.seq (wp_srl (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain pk₁ : PK s s₁ := PK.ofUpd u₁
  obtain E₁ := E.of_pk pk₁
  obtain hP₁ := hP.of_eq pk₁.rd pk₁.wr
  obtain r19 : s₁.gpr .s6 = P := by rw [u₁.other _ (by decide), h19]
  obtain r20 : s₁.gpr .s7 = BitVec.ofNat 64 n := by rw [u₁.other _ (by decide), h20]
  obtain r9 : s₁.gpr .t0 = BitVec.ofNat 64 (n / 16) := by rw [u₁.gpr, h20, ofNat_lsr4' hn]
  have m₁ : s₁.mem = s.mem := u₁.mem
  refine WP.ite (decide (n / 16 = 0)) (eval_zero_ofNat _ _ (by omega_using [hn]) r9) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : n / 16 = 0 := by simpa using ht
    refine WP.mono (short_wp L E₁ hP₁ (by omega_using [h0]) r19 r20 hout) fun s' ⟨pk, f, o⟩ => ⟨pk₁.trans pk, ?_, ?_⟩
    · rw [← m₁]; exact f
    · rw [o, m₁]
  · have h0 : n / 16 ≠ 0 := by simpa using hf
    refine WP.mono (long_wp L E₁ hP₁ (by omega_using [h0]) r19 r20 hout) fun s' ⟨pk, f, o⟩ => ⟨pk₁.trans pk, ?_, ?_⟩
    · rw [← m₁]; exact f
    · rw [o, m₁]

end VG.Proof.AesSiv.RISCV64
