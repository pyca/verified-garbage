module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Mac
public import VerifiedGarbage.Spec.Siv.Contract
public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Subkeys
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.CmacAes.PPC64LE.FinSteps
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp

/-!
# AES-SIV on PPC64LE: S2V over the components of associated data

Untrusted: everything here is checked by Lean. S2V starts with
`D = AES-CMAC(K1, <zero>)`, a finalization of the zero block at `W + 16`
from a zero state at `W + 272` (`start_wp`). The `N` descriptors at `A`
(16 bytes each: an address and a length) list the components in the memory
`m` (`descW`, `Ads`). Each iteration of `s2vAds` loads the next descriptor
(`adNext`), computes the CMAC of its component into the state at `W + 240`
(`cmacOf_wp`) and folds it into `D` (`adStep_wp`), so `D` is S2V's state of
the components so far (`AInv`, `aStep_wp`), and of all of them after the
loop (`s2vAds_wp`). The code writes only within `W` from byte 16 to 128 and
from byte 240 on (`wR`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.Impl.AesSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor Upd Mupd
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_subi wp_li wp_ld)
open VG.Proof.CmacAes.Stream.PPC64LE (FArgs)
open VG.Proof.AesCcm.PPC64LE (wp_mv)
open VG.Spec.Aes (bytesAt)

/-- What S2V writes: `W` from byte 16 to 128 and from byte 240 on. -/
abbrev wR (c : Cx) : List Region := [⟨c.W + BitVec.ofNat 64 16, 112⟩, ⟨c.W + BitVec.ofNat 64 240, 2336⟩]

theorem macR_wR {c : Cx} {st : Nat} (h : 240 ≤ st) (h' : st + 16 ≤ 384) :
    ∀ r ∈ macR c st, ∃ r' ∈ wR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ h (by omega)⟩
  · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ (by decide) (by decide)⟩

theorem w16_wR {c : Cx} {d : Nat} (h : 240 ≤ d ∨ (16 ≤ d ∧ d + 16 ≤ 128)) (h' : d + 16 ≤ 2576) :
    ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 d, 16⟩ : Region)], ∃ r' ∈ wR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rcases h with h | ⟨h₁, h₂⟩
  · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ h (by omega)⟩
  · exact ⟨⟨c.W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ h₁ (by omega)⟩

/-- A region apart from `W` is apart from `wR`. -/
theorem dis_wR {c : Cx} {r : Region} (hw : r.Disjoint ⟨c.W, 2576⟩) : ∀ r' ∈ wR c, r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))

/-! ## S2V's first state -/

/-- `startPre`: the zero block and `D` zeroed, and the arguments of the
finalization of the zero block. -/
theorem startPre_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block startPre) s fun s' => MacKeep s s' ∧
      s'.mem = Proof.Cmac.zero2 (Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 zO)) (c.W + BitVec.ofNat 64 dO) ∧
      FArgs s' c.C (c.W + BitVec.ofNat 64 dO) (c.W + BitVec.ofNat 64 zO) (c.W + BitVec.ofNat 64 384) 16 c.R := by
  simp only [startPre, List.append_assoc]
  refine zero16_wp E (d := zO) (by decide) (by decide) fun s₁ pk₁ g₁ m₁ => ?_
  have E₁ := E.of_pk pk₁
  refine zero16_wp E₁ (d := dO) (by decide) (by decide) fun s₂ pk₂ g₂ m₂ => ?_
  have E₂ := E₁.of_pk pk₂
  unfold macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by decide) (by decide) fun t₃ v₃ =>
    wp_addi (by decide) (by decide) fun t₄ v₄ => wp_addi (by decide) (by decide) fun t₅ v₅ =>
    wp_li (by decide) fun t₆ v₆ => WP.block_nil ?_
  have K : MacKeep s₂ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
  have K₀ : MacKeep s s₂ := ⟨pk₁.trans pk₂, by rw [g₂ _ (by decide), g₁ _ (by decide)],
    by rw [g₂ _ (by decide), g₁ _ (by decide)], by rw [g₂ _ (by decide), g₁ _ (by decide)],
    by rw [g₂ _ (by decide), g₁ _ (by decide)]⟩
  have E₆ := E₂.of_pk K.pk
  refine ⟨K₀.trans K, by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, m₂, m₁], ?_⟩
  exact fargs L E₆ (y := dO) (by decide) (Nat.le_refl 16) (L.srcW E₆.perm (t := zO) (k := 16) (by decide))
    (L.w_w (.inl (by decide)) (by decide) (by decide))
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E₂.r15])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E₂.r16])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E₂.r14])
    (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₂.r14])
    (by rw [v₆.gpr])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₂.r14]; rfl)

theorem siv_zero : Spec.Siv.zero = Spec.Cmac.zeros 16 := rfl

/-- `D = AES-CMAC(K1, <zero>)`, S2V's first state, at `W + 272`. -/
theorem start_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.seq (.block startPre) Impl.CmacAes.Stream.PPC64LE.finCall) s fun s' => MacKeep s s' ∧
      Frame (wR c) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 dO) 16 = Spec.Siv.s2vStart (Spec.Siv.ctxMac s.mem c.C c.R) := by
  have hRb := L.rb
  refine WP.seq (WP.mono (startPre_wp L E) fun s₁ ⟨K₁, m₁, F⟩ => ?_)
  refine WP.mono (fin_call_raw F) fun s₂ h₂ => ?_
  have f₁ : Frame (wR c) s.mem s₁.mem := by
    rw [m₁]
    exact ((Proof.Cmac.frame_store2 _ _ _).sub (w16_wR (.inr ⟨by decide, by decide⟩) (by decide))).trans
      ((Proof.Cmac.frame_store2 _ _ _).sub (w16_wR (.inl (by decide)) (by decide)))
  refine ⟨K₁.trans (MacKeep.ofSaved h₂.rd h₂.wr h₂.sp h₂.saved),
    f₁.trans (h₂.frame.sub (macR_wR (st := dO) (by decide) (by decide))), ?_⟩
  -- What the call reads.
  have dC : ∀ {d k : Nat}, d + k ≤ 512 → ∀ r ∈ wR c, (⟨c.C + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd => dis_wR (L.c_w.sub_left (Lay.cSub hd))
  have cK {d k : Nat} (hd : d + k ≤ 512) :
      bytesAt s₁.mem (c.C + BitVec.ofNat 64 d) k = bytesAt s.mem (c.C + BitVec.ofNat 64 d) k :=
    Proof.Cmac.bytesAt_frame f₁ (dC hd) (by omega)
  have sch := cK (d := 0) (k := 16 * (c.R + 1)) (by omega)
  rw [BitVec.add_zero] at sch
  have hz : bytesAt s₁.mem (c.W + BitVec.ofNat 64 zO) 16 = Spec.Cmac.zeros 16 := by
    have fz : Frame [⟨c.W + BitVec.ofNat 64 dO, 16⟩] (Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 zO))
        (Proof.Cmac.zero2 (Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 zO)) (c.W + BitVec.ofNat 64 dO)) :=
      Proof.Cmac.frame_store2 _ _ _
    have dz : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 dO, 16⟩ : Region)],
        (⟨c.W + BitVec.ofNat 64 zO, 16⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    rw [m₁, Proof.Cmac.bytesAt_frame fz dz (by decide), Proof.Cmac.zero2_bytes]
  have hd : bytesAt s₁.mem (c.W + BitVec.ofNat 64 dO) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero2_bytes]
  rw [h₂.out, Proof.CmacAes.PPC64LE.mn, Proof.CmacAes.PPC64LE.ciphAt, sch, cK (d := 240) (k := 16) (by decide),
    cK (d := 256) (k := 16) (by decide), hz, hd, Spec.Siv.s2vStart, Spec.Siv.ctxMac, Spec.Siv.schedCiph,
    Siv.cmacWith_chained, siv_zero]
  rfl

/-! ## The descriptors -/

/-- An access within a region the permissions cover, for a region of at
most `2⁶⁴` bytes. -/
theorem in_off_le {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k ≤ 2 ^ 64) (hn : 0 < n) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  h _ _ ⟨_, List.mem_singleton_self _, by
    simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hd⟩

/-- Word `j` (0: the address, 1: the length) of descriptor `i` at `A`, in `m`. -/
abbrev descW (m : Mem) (A : Addr) (i j : Nat) : BitVec 64 := m.readW (A + BitVec.ofNat 64 (16 * i + 8 * j)) 64

/-- The `i`-th component, `i < N`. -/
theorem components_getElem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (Spec.Siv.components 64 m A N)[i]'(by simp [Spec.Siv.components, Sig.listed, hi]) =
      bytesAt m (descW m A i 0) (descW m A i 1).toNat := by
  simp only [Spec.Siv.components, Sig.listed, List.getElem_map, List.getElem_range, Elem.size, Nat.mul_one,
    descW, BitVec.setWidth_eq]
  rw [show i * (2 * (64 / 8)) = 16 * i + 8 * 0 by omega, show (64 / 8 : Nat) = 8 from rfl, Offset.add_add,
    show 16 * i + 8 * 0 + 8 = 16 * i + 8 * 1 by omega]

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
`i`, `r17` and `r18` the next descriptor's address and how many are left. -/
structure AInv (c : Cx) (σ : State) (i : Nat) (s : State) : Prop where
  env : Env c s
  pk : PK σ s
  ads : Ads c σ.mem s
  r17 : s.gpr .r17 = c.A + BitVec.ofNat 64 (16 * i)
  r18 : s.gpr .r18 = BitVec.ofNat 64 (c.N - i)
  frame : Frame (wR c) σ.mem s.mem
  acc : bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac σ.mem c.C c.R) ((Spec.Siv.components 64 σ.mem c.A c.N).take i)

/-- What `adNext` keeps. -/
structure NextKeep (s s' : State) : Prop where
  pk : PK s s'
  r17 : s'.gpr .r17 = s.gpr .r17
  r18 : s'.gpr .r18 = s.gpr .r18
  mem : s'.mem = s.mem

/-- `adNext`: the address and the length of descriptor `i`'s component in
`r19` and `r20`. -/
theorem adNext_wp {c : Cx} (L : Lay c) {σ s : State} {i : Nat} (h : AInv c σ i s) (hi : i < c.N) :
    WP isa (.block adNext) s fun s' => s'.gpr .r19 = descW σ.mem c.A i 0 ∧
      s'.gpr .r20 = descW σ.mem c.A i 1 ∧ NextKeep s s' := by
  have aw := L.aw
  have dA : ∀ {d : Nat}, d + 8 ≤ 16 * c.N → ∀ r ∈ wR c, (⟨c.A + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r :=
    fun hd => dis_wR (L.a_w.sub_left (Offset.sub_base _ hd))
  have a₀ : s.gpr .r17 + BitVec.ofNat 64 0 = c.A + BitVec.ofNat 64 (16 * i + 8 * 0) := by
    rw [h.r17, Offset.add_add, show 16 * i + 0 = 16 * i + 8 * 0 by omega]
  have a₁ : s.gpr .r17 + BitVec.ofNat 64 8 = c.A + BitVec.ofNat 64 (16 * i + 8 * 1) := by
    rw [h.r17, Offset.add_add, show 16 * i + 8 = 16 * i + 8 * 1 by omega]
  have i₀ : InRegions (s.rd ++ s.wr) (c.A + BitVec.ofNat 64 (16 * i + 8 * 0)) 8 :=
    in_off_le h.env.perm.a (by omega) (by omega) (by decide)
  have i₁ : InRegions (s.rd ++ s.wr) (c.A + BitVec.ofNat 64 (16 * i + 8 * 1)) 8 :=
    in_off_le h.env.perm.a (by omega) (by omega) (by decide)
  have v₀ : s.mem.readW (c.A + BitVec.ofNat 64 (16 * i + 8 * 0)) 64 = descW σ.mem c.A i 0 :=
    (h.frame.readW (r := ⟨c.A + BitVec.ofNat 64 (16 * i + 8 * 0), 8⟩) (Region.contains_self _ _)
      (dA (by omega)) (by decide))
  have v₁ : s.mem.readW (c.A + BitVec.ofNat 64 (16 * i + 8 * 1)) 64 = descW σ.mem c.A i 1 :=
    (h.frame.readW (r := ⟨c.A + BitVec.ofNat 64 (16 * i + 8 * 1), 8⟩) (Region.contains_self _ _)
      (dA (by omega)) (by decide))
  unfold adNext
  refine wp_ld (a := c.A + BitVec.ofNat 64 (16 * i + 8 * 0)) (by decide) (by decide) a₀ i₀ fun s₁ u₁ => ?_
  refine wp_ld (a := c.A + BitVec.ofNat 64 (16 * i + 8 * 1)) (by decide) (by decide)
    (by rw [u₁.other _ (by decide)]; exact a₁) (by rw [u₁.rd, u₁.wr]; exact i₁) fun s₂ u₂ => WP.block_nil ?_
  exact ⟨by rw [u₂.other _ (by decide), u₁.gpr, v₀], by rw [u₂.gpr, u₁.mem, v₁],
    ⟨PK.trans (PK.ofUpd u₁) (PK.ofUpd u₂), by rw [u₂.other _ (by decide), u₁.other _ (by decide)],
      by rw [u₂.other _ (by decide), u₁.other _ (by decide)], by rw [u₂.mem, u₁.mem]⟩⟩

/-! ## The context's PRF and cipher, after writes apart from it -/

theorem ctxMac_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxMac m' C R = Spec.Siv.ctxMac m C R := by
  unfold Spec.Siv.ctxMac Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega))) (by omega),
    Proof.Cmac.bytesAt_frame hf (p := C + 240)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 240) (n := 16) (by decide))) (by decide),
    Proof.Cmac.bytesAt_frame hf (p := C + 256)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 256) (n := 16) (by decide))) (by decide)]

theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxCiph m' C R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (p := C + 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega))) (by omega)]

/-! ## A step of the loop -/

/-- The memory after `adStep`: `D = dbl(D) ⊕` the CMAC state. -/
def stepMem (m : Mem) (W : Addr) : Mem :=
  Proof.Cmac.xor2Mem (Proof.CmacAes.PPC64LE.dblMem m W dO dO) (W + BitVec.ofNat 64 dO) (W + BitVec.ofNat 64 dO)
    (W + BitVec.ofNat 64 stO)

theorem stepMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 dO, 16⟩] m (stepMem m W) := by
  unfold stepMem
  exact (Proof.CmacAes.PPC64LE.dblMem_frame m W dO dO).trans (Proof.Cmac.xor2Mem_frame _ _ _ _)

theorem stepMem_bytes {c : Cx} (L : Lay c) (m : Mem) :
    bytesAt (stepMem m c.W) (c.W + BitVec.ofNat 64 dO) 16 =
      Spec.Cmac.xor (Spec.Cmac.dbl 16 (bytesAt m (c.W + BitVec.ofNat 64 dO) 16))
        (bytesAt m (c.W + BitVec.ofNat 64 stO) 16) := by
  unfold stepMem
  rw [Proof.Cmac.xor2Mem_bytes _ (by
      rw [Offset.add_add]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by rw [Offset.add_add]; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
    Proof.CmacAes.PPC64LE.dblMem_bytes,
    Proof.Cmac.bytesAt_frame (Proof.CmacAes.PPC64LE.dblMem_frame m c.W dO dO) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)]

/-- `adStep`, but for the stack pointer. -/
theorem adStep_wp' {c : Cx} {s : State} (E : Env c s) {i k : Nat} (hk : 1 ≤ k) (hk64 : k < 2 ^ 64)
    (h17 : s.gpr .r17 = c.A + BitVec.ofNat 64 (16 * i)) (h18 : s.gpr .r18 = BitVec.ofNat 64 k) :
    WP isa (.block adStep) s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ keepRegs, s'.gpr r = s.gpr r) ∧
      s'.gpr .r17 = c.A + BitVec.ofNat 64 (16 * (i + 1)) ∧
      s'.gpr .r18 = BitVec.ofNat 64 (k - 1) ∧ s'.mem = stepMem s.mem c.W := by
  unfold adStep
  rw [List.append_assoc]
  refine Proof.CmacAes.PPC64LE.dbl_wp E.r14 (by decide) (by decide) (E.perm.wR (by decide))
    (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide)) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  have r14₁ : s₁.gpr .r14 = c.W := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.r14]
  have P₁ := E.perm.of_eq rd₁ wr₁
  show WP isa (.block (Proof.CmacAes.PPC64LE.xor2 .r14 .r14 .r14 dO stO dO ++ _)) s₁ _
  refine Proof.CmacAes.PPC64LE.xor2_wp .r14 .r14 .r14 dO stO dO (P := c.W + BitVec.ofNat 64 dO)
    (Q := c.W + BitVec.ofNat 64 stO) (C := c.W + BitVec.ofNat 64 dO) ⟨by decide, by decide, by decide⟩
    (by decide) (by decide) (by decide) (by rw [r14₁]) (by rw [r14₁, Offset.add_add]) (by rw [r14₁])
    (by rw [r14₁, Offset.add_add]) (by rw [r14₁]) (by rw [r14₁, Offset.add_add]) (by decide)
    (P₁.wR (by decide)) (by rw [Offset.add_add]; exact P₁.wR (by decide)) (P₁.wR (by decide))
    (by rw [Offset.add_add]; exact P₁.wR (by decide)) (P₁.wW (by decide))
    (by rw [Offset.add_add]; exact P₁.wW (by decide)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_subi (by decide) (by decide) fun s₄ u₄ =>
    WP.block_nil ⟨by rw [u₄.rd, u₃.rd, rd₂, rd₁], by rw [u₄.wr, u₃.wr, wr₂, wr₁], fun r hr => ?_, ?_, ?_, ?_⟩
  · have h9 : r ≠ .r9 := fun e => by subst e; exact absurd hr (by decide)
    have h10 : r ≠ .r10 := fun e => by subst e; exact absurd hr (by decide)
    have h11 : r ≠ .r11 := fun e => by subst e; exact absurd hr (by decide)
    have h12 : r ≠ .r12 := fun e => by subst e; exact absurd hr (by decide)
    have h17 : r ≠ .r17 := fun e => by subst e; exact absurd hr (by decide)
    have h18 : r ≠ .r18 := fun e => by subst e; exact absurd hr (by decide)
    rw [u₄.other _ h18, u₃.other _ h17, g₂ _ h9 h10, g₁ _ h9 h10 h11 h12]
  · rw [u₄.other _ (by decide), u₃.gpr, g₂ _ (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide), h17, Offset.add_add]
    congr 2
  · rw [u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide), h18]
    exact ofNat_sub' hk hk64
  · rw [u₄.mem, u₃.mem, m₂, m₁]; rfl

/-- `adStep`: `D = dbl(D) ⊕` the CMAC state; the next descriptor, and one
fewer left. -/
theorem adStep_wp {c : Cx} {s : State} (E : Env c s) {i k : Nat} (hk : 1 ≤ k) (hk64 : k < 2 ^ 64)
    (h17 : s.gpr .r17 = c.A + BitVec.ofNat 64 (16 * i)) (h18 : s.gpr .r18 = BitVec.ofNat 64 k) :
    WP isa (.block adStep) s fun s' => PK s s' ∧ s'.gpr .r17 = c.A + BitVec.ofNat 64 (16 * (i + 1)) ∧
      s'.gpr .r18 = BitVec.ofNat 64 (k - 1) ∧ s'.mem = stepMem s.mem c.W :=
  WP.mono (VG.Proof.AesCbc.PPC64LE.wp_sp (adStep_wp' E hk hk64 h17 h18))
    fun _ ⟨⟨rd, wr, g, r17, r18, m⟩, sp⟩ => ⟨⟨rd, wr, sp, g⟩, r17, r18, m⟩

/-! ## The loop -/

/-- One iteration of the loop, for the component `i < N`. -/
theorem aStep_wp {c : Cx} (L : Lay c) {σ s : State} {i : Nat} (h : AInv c σ i s) (hi : i < c.N) :
    WP isa (.seq (.block adNext) (.seq (cmacOf stO) (.block adStep))) s (AInv c σ (i + 1)) := by
  have aw := L.aw
  have hRb := L.rb
  refine WP.seq (WP.mono (adNext_wp L h hi) fun s₁ ⟨h19₁, h20₁, k₁⟩ => ?_)
  have E₁ := h.env.of_pk k₁.pk
  have hP : Buf c s₁ (descW σ.mem c.A i 0) (descW σ.mem c.A i 1).toNat := (h.ads i hi).of_eq k₁.pk.rd k₁.pk.wr
  refine WP.seq (WP.mono (cmacOf_wp L E₁ (st := stO) (by decide) (by decide) hP h19₁ (by rw [h20₁]; simp))
    fun s₂ ⟨K₂, f₂, out₂⟩ => ?_)
  have E₂ := E₁.of_pk K₂.pk
  have h17₂ : s₂.gpr .r17 = c.A + BitVec.ofNat 64 (16 * i) := by rw [K₂.r17, k₁.r17, h.r17]
  have h18₂ : s₂.gpr .r18 = BitVec.ofNat 64 (c.N - i) := by rw [K₂.r18, k₁.r18, h.r18]
  refine WP.mono (adStep_wp E₂ (i := i) (k := c.N - i) (by omega) (by omega) h17₂ h18₂)
    fun s₃ ⟨pk₃, h17₃, h18₃, m₃⟩ => ?_
  -- The memory.
  have f₀₂ : Frame (wR c) σ.mem s₂.mem := h.frame.trans (by rw [← k₁.mem]; exact f₂.sub (macR_wR (by decide)
    (by decide)))
  have f₂₃ : Frame (wR c) s₂.mem s₃.mem := by
    rw [m₃]; exact (stepMem_frame _ _).sub (w16_wR (.inl (by decide)) (by decide))
  have dc : ∀ r ∈ wR c, (⟨c.C, 512⟩ : Region).Disjoint r := dis_wR L.c_w
  have mac₁ : Spec.Siv.ctxMac s₁.mem c.C c.R = Spec.Siv.ctxMac σ.mem c.C c.R := by
    rw [k₁.mem]; exact ctxMac_frame h.frame dc hRb
  have comp₁ : bytesAt s₁.mem (descW σ.mem c.A i 0) (descW σ.mem c.A i 1).toNat =
      bytesAt σ.mem (descW σ.mem c.A i 0) (descW σ.mem c.A i 1).toNat := by
    rw [k₁.mem]; exact Proof.Cmac.bytesAt_frame h.frame (dis_wR (h.ads i hi).w) (by have := (h.ads i hi).lt; omega)
  have dD₂ : bytesAt s₂.mem (c.W + BitVec.ofNat 64 dO) 16 = bytesAt s₁.mem (c.W + BitVec.ofNat 64 dO) 16 := by
    refine Proof.Cmac.bytesAt_frame f₂ (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have hl := length_components σ.mem c.A c.N
  refine ⟨E₂.of_pk pk₃, (h.pk.trans k₁.pk).trans (K₂.pk.trans pk₃),
    h.ads.of_eq (by rw [pk₃.rd, K₂.pk.rd, k₁.pk.rd]) (by rw [pk₃.wr, K₂.pk.wr, k₁.pk.wr]), h17₃, ?_,
    f₀₂.trans f₂₃, ?_⟩
  · rw [h18₃, Nat.sub_sub]
  · rw [m₃, stepMem_bytes L, out₂, dD₂, mac₁, comp₁, k₁.mem, h.acc, List.take_succ_eq_append_getElem (by omega),
      s2vAcc_snoc, components_getElem σ.mem c.A hi]
    rfl

/-- S2V over all the components, from S2V's first state in `D`. -/
theorem s2vAds_wp {c : Cx} (L : Lay c) {σ s : State} (h : AInv c σ 0 s) :
    WP isa s2vAds s (AInv c σ c.N) := by
  have aw := L.aw
  have hN : c.N < 2 ^ 64 := by omega
  have h18 : s.gpr .r18 = BitVec.ofNat 64 c.N := by rw [h.r18, Nat.sub_zero]
  unfold s2vAds
  refine WP.ite (decide (c.N = 0)) (VG.Proof.Gather.PPC64LE.eval_zero h18 hN) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.N = 0 := by simpa using ht
    exact WP.block_nil (by rw [h0]; exact h)
  · have h0 : c.N ≠ 0 := by simpa using hf
    refine WP.loop (M := isa) (fun (n : Nat) (t : State) => ∃ j, n = c.N - j ∧ j < c.N ∧ AInv c σ j t)
      ?_ (c.N - 0) s ⟨0, rfl, by omega, h⟩
    rintro n t ⟨j, rfl, hj, hI⟩
    refine WP.mono (aStep_wp L hI hj) fun t' hI' => ?_
    have ev := VG.Proof.Gather.PPC64LE.eval_nonzero hI'.r18 (by omega)
    by_cases hz : c.N - (j + 1) = 0
    · left
      refine ⟨by rw [ev]; simp [hz], ?_⟩
      have e : j + 1 = c.N := by omega
      rw [e] at hI'; exact hI'
    · right
      exact ⟨by rw [ev]; simp [hz], c.N - (j + 1), by omega, j + 1, rfl, by omega, hI'⟩

end VG.Proof.AesSiv.PPC64LE
