module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
public import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-GCM on PPC64LE: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/J0.lean`): `j0` writes `J₀` for the `r25`-byte nonce at
`r24` to the state: its words and `0x00000001` for a 12-byte nonce
(`j012_ok`), and otherwise GHASH of the nonce padded with zeros and the
lengths block, with `absorb`, `flush` and `lens` on the accumulator at the
state's first block (`j0hash_ok`), the nonce's length in `r18`. `initState`
then zeroes the accumulator and writes the first counter block `inc₃₂(J₀)`
(`initState_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

theorem inc32_words (a b c d : BitVec 32) : inc32 (a ++ b ++ c ++ d) = a ++ b ++ c ++ (d + 1) := by
  have h₁ : (a ++ b ++ c ++ d).extractLsb' 32 96 = a ++ b ++ c := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    simp only [show ¬ (32 + i < 32) by omega, ite_false, show 32 + i - 32 = i by omega]
  have h₂ : (a ++ b ++ c ++ d).extractLsb' 0 32 = d := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hi]
  simp only [inc32, h₁, h₂]

theorem le4_one : le4 (BitVec.ofNat 32 0x01000000) = [0, 0, 0, 1] := by decide

/-- A block from the bytes of its four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = byteRev32 a ++ byteRev32 b ++ byteRev32 c ++ byteRev32 d := by
  have h := Proof.Cmac.le4_rev4 (byteRev32 a) (byteRev32 b) (byteRev32 c) (byteRev32 d)
  rw [Proof.Cmac.byteRev32_byteRev32, Proof.Cmac.byteRev32_byteRev32, Proof.Cmac.byteRev32_byteRev32,
    Proof.Cmac.byteRev32_byteRev32] at h
  rw [h, Proof.Cmac.ofBytes_toBytes]

theorem rev32_eq : VG.PPC64LE.rev32 = byteRev32 := rfl

theorem read_4 (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp only [Mem.readW]; exact (BitVec.setWidth_eq _).symm

theorem write_4 (m : Mem) (a : Addr) (v : BitVec 32) : m.write a 4 v = m.writeW a v := by
  simp only [Mem.writeW]; exact congrArg (m.write a 4) (BitVec.setWidth_eq _).symm

theorem ww32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt this]

theorem ww32_add1 (x : BitVec 32) : (x.setWidth 64 + 1).setWidth 32 = x + 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_mod_of_dvd _ (by decide)]
  rfl

theorem ww32_add1' (x : BitVec 32) : (x.setWidth 64 + BitVec.ofNat 64 1).setWidth 32 = x + 1 :=
  ww32_add1 x

theorem lis_one : (((0x0100 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64).setWidth 32 =
    BitVec.ofNat 32 0x01000000 := by decide

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

/-- The regions `j0` writes. -/
abbrev j0Frame (st w : Addr) : List Region :=
  [⟨st, 80⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩]

/-- Before `j0`: the `n`-byte nonce at `Np`, its length also in `r18`. -/
structure J0In (V : Reg → BitVec 64) (sp : Addr) (H : Block) (Np : Addr) (n : Nat) (s : State) : Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H
  r24 : s.gpr .r24 = Np
  r25 : s.gpr .r25 = BitVec.ofNat 64 n
  r18 : V .r18 = BitVec.ofNat 64 n
  data : DataOk (V .r30) (V .r31) s Np n

/-- `J₀` written, from `m₀`. -/
structure J0Mid (V : Reg → BitVec 64) (sp : Addr) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (V .r30) = Spec.Gcm.j0 H iv
  frame : Frame (j0Frame (V .r30) (V .r31)) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (V : Reg → BitVec 64) (sp : Addr) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env V sp s
  hH : blockAt s.mem (V .r29 + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (V .r30) = Spec.Gcm.j0 H iv
  y : blockAt s.mem (V .r30 + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (V .r30 + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (j0Frame (V .r30) (V .r31)) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
include L

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨V .r30 + BitVec.ofNat 64 d, k⟩] m m')
    (hk : d + k ≤ 80) : Frame (j0Frame (V .r30) (V .r31)) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Lay.stSub hk⟩

/-- `J₀` of a 12-byte nonce. -/
theorem j012_ok {H : Block} {Np : Addr} {s : State} (h : J0In V sp H Np 12 s) :
    WP isa (.block j012) s (J0Mid V sp H (bytesAt s.mem Np 12) s.mem) := by
  have he := h.env
  have h30 := he.r30
  have hd := h.data
  have r₀ := in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  have r₁ := in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  have r₂ := in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  have w₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  simp only [add_ofNat_zero] at r₀ w₀
  have h24 := h.r24
  have hrun : WP isa (.block j012) s fun s' =>
      s'.mem = store4 s.mem (V .r30) (s.mem.readW Np 32)
        (s.mem.readW (Np + BitVec.ofNat 64 4) 32) (s.mem.readW (Np + BitVec.ofNat 64 8) 32)
        (BitVec.ofNat 32 0x01000000) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps' s s' := by
    apply WP.of_runBlock
    simp only [j012, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
      State.write, Size.bytes, h24, h30, r₀, r₁, r₂, w₀, w₁, w₂, w₃, read_4, write_4, Option.bind_some,
      Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ne_eq, add_ofNat_zero,
      not_false_eq_true, Nat.reduceLT, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, ↓reduceIte, and_self,
      implies_true]
    refine ⟨by rw [ww32, ww32, ww32, lis_one]; rfl, fun r a b c d => by simp [a, b, c, d], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono hrun fun s' ⟨hm, hg, hk⟩ => ?_
  have f : Frame [⟨V .r30 + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem := by
    rw [hm, add_ofNat_zero]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine ⟨he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr, ?_, ?_, st_j0Frame f (by decide)⟩
  · rw [blockAt_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
  · have hb : bytesAt s.mem Np 12 = bytesAt s.mem Np 4 ++
        bytesAt s.mem (Np + BitVec.ofNat 64 4) 4 ++ bytesAt s.mem (Np + BitVec.ofNat 64 8) 4 := by
      rw [show (12 : Nat) = 4 + 8 from rfl, bytesAt_add, show (8 : Nat) = 4 + 4 from rfl, bytesAt_add,
        add_ofNat_assoc, List.append_assoc]
    rw [Proof.Gcm.j0_12 _ (length_bytesAt _ _ _), blockAt, hm, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW,
      Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, le4_one, hb]

/-- The first counter block, and the accumulator zeroed. -/
theorem initState_ok {H : Block} {iv : List Byte} {m₀ : Mem} {s : State} (h : J0Mid V sp H iv m₀ s) :
    WP isa (.block initState) s (J0Out V sp H iv m₀) := by
  have he := h.env
  have h30 := he.r30
  have r₀ := he.perm.stR (show 0 + 4 ≤ 80 by decide)
  have r₁ := he.perm.stR (show 4 + 4 ≤ 80 by decide)
  have r₂ := he.perm.stR (show 8 + 4 ≤ 80 by decide)
  have r₃ := he.perm.stR (show 12 + 4 ≤ 80 by decide)
  simp only [add_ofNat_zero] at r₀
  have w₀ := he.perm.stW (show 48 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 52 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 56 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 60 + 4 ≤ 80 by decide)
  have z₀ := he.perm.stW (show 16 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 24 + 8 ≤ 80 by decide)
  generalize hw : s.mem.readW (V .r30 + BitVec.ofNat 64 12) 32 = w3
  have hrun : WP isa (.block initState) s fun s' =>
      s'.mem = ((store4 s.mem (V .r30 + BitVec.ofNat 64 48) (s.mem.readW (V .r30) 32)
        (s.mem.readW (V .r30 + BitVec.ofNat 64 4) 32) (s.mem.readW (V .r30 + BitVec.ofNat 64 8) 32)
        (byteRev32 (byteRev32 w3 + 1))).writeW (V .r30 + BitVec.ofNat 64 16) (0 : BitVec 64)).writeW
          (V .r30 + BitVec.ofNat 64 24) (0 : BitVec 64) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
    apply WP.of_runBlock
    simp only [initState, runBlock_cons, runStep_some, runBlock_nil, exec, addr, addrX, State.load, State.store,
      State.write, State.read, Size.bytes, Size.bits, h30, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, z₀, z₁, read_4, write_4,
      write_8, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ne_eq,
      BitVec.add_zero, BitVec.ofNat_eq_ofNat, not_false_eq_true, Nat.reduceLT, Nat.reducePow,
      Nat.reduceMul, Nat.reduceMod, ↓reduceIte, and_self, implies_true, hw]
    refine ⟨by simp only [ww32, ww32_add1', rev32_eq, BitVec.setWidth_eq, store4, add_ofNat_assoc, Nat.reduceAdd]; rfl,
      fun r a b c d e f => by simp [a, b, c, d, e, f], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono hrun fun s' ⟨hm, hg, hk⟩ => ?_
  obtain ⟨m₁, hm₁⟩ : ∃ m₁, m₁ = store4 s.mem (V .r30 + BitVec.ofNat 64 48) (s.mem.readW (V .r30) 32)
      (s.mem.readW (V .r30 + BitVec.ofNat 64 4) 32) (s.mem.readW (V .r30 + BitVec.ofNat 64 8) 32)
      (byteRev32 (byteRev32 w3 + 1)) := ⟨_, rfl⟩
  rw [← hm₁] at hm
  have e24 : V .r30 + BitVec.ofNat 64 24 = V .r30 + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 := by
    simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [e24] at hm
  have f₄ : Frame [⟨V .r30 + BitVec.ofNat 64 48, 16⟩] s.mem m₁ := by
    rw [hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have fz : Frame [⟨V .r30 + BitVec.ofNat 64 16, 16⟩] m₁ s'.mem := by
    rw [hm]; exact Proof.Cmac.frame_store2 _ _ _
  have dz : (⟨V .r30 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨V .r30 + BitVec.ofNat 64 16, 16⟩ :=
    Lay.st_st (.inr (by decide)) (by decide) (by decide)
  have ff : Frame [⟨V .r30 + BitVec.ofNat 64 0, 80⟩] s.mem s'.mem := by
    refine (f₄.sub fun r hr => ?_).trans (fz.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hJ : blockAt s'.mem (V .r30) = blockAt s.mem (V .r30) := by
    rw [blockAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.st_st (st := V .r30) (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide))
          (by decide) (by decide)),
      blockAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.st_st (st := V .r30) (a := 0) (n := 16) (d := 48) (k := 16) (.inl (by decide))
          (by decide) (by decide))]
  refine ⟨he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr, ?_,
    by rw [hJ, h.j0], ?_, ?_, h.frame.trans (st_j0Frame ff (by decide))⟩
  · rw [blockAt_frame ff (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, hm, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; decide
  · rw [blockAt, bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dz) (by decide),
      hm₁, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, ← h.j0,
      blockAt, Proof.Cmac.ofBytes_rev4, ← Proof.Cmac.le4_readW s.mem (V .r30), ← Proof.Cmac.le4_readW,
      ← Proof.Cmac.le4_readW, ofBytes_le4, hw, Proof.Cmac.byteRev32_byteRev32, inc32_words]

omit L in
theorem abs_j0Frame {m m' : Mem} (h : Frame (absFrame (V .r30) (V .r31) 0) m m') :
    Frame (j0Frame (V .r30) (V .r31)) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (tFrame (V .r30) (V .r31) 0) m m') :
    Frame (j0Frame (V .r30) (V .r31)) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- The first block of `j0hash`: the accumulator at the state zeroed. -/
theorem j0zero_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In V sp H Np n s) :
    WP isa (.block [.li .r0 0, .store .d .r0 .r30 0, .store .d .r0 .r30 8, .li .r26 0]) s
      (fun s' => AbsIn V sp 0 H [] Np n s' ∧
        blockAt s'.mem (V .r30 + BitVec.ofNat 64 0) = 0 ∧
        bytesAt s'.mem Np n = bytesAt s.mem Np n ∧
        Frame [⟨V .r30 + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem) := by
  have he := h.env
  have hd := h.data
  have h30 := he.r30
  have z₀ := he.perm.stW (show 0 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 8 + 8 ≤ 80 by decide)
  have hrun : WP isa (.block [.li .r0 0, .store .d .r0 .r30 0, .store .d .r0 .r30 8, .li .r26 0]) s
      fun s' => s'.mem = (s.mem.writeW (V .r30 + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW
          (V .r30 + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
        s'.gpr .r26 = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .r0 → r ≠ .r26 → s'.gpr r = s.gpr r) ∧ Keeps' s s' := by
    simp only [add_ofNat_zero] at z₀ ⊢
    crun [h30, z₀, z₁, write_8]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono hrun fun s₁ ⟨hm₁, h26, hg₁, hk₁⟩ => ?_
  have f₁ : Frame [⟨V .r30 + BitVec.ofNat 64 0, 16⟩] s.mem s₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ r ∈ [(⟨V .r30 + BitVec.ofNat 64 0, 16⟩ : Region)], (⟨Np, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hd.st.sub_right (Lay.stSub (by decide))
  refine ⟨⟨he.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr,
    by rw [hg₁ _ (by decide) (by decide), h.r24], by rw [hg₁ _ (by decide) (by decide), h.r25],
    by rw [h26]; rfl, hd.of_eq hk₁.rd hk₁.wr, ?_⟩, ?_, bytesAt_frame f₁ dD (by have := hd.lt; omega), f₁⟩
  · rw [blockAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, hm₁, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; decide

/-- `J₀` of a nonce of any length but 12: GHASH of the nonce padded and of
the lengths block. -/
theorem j0hash_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In V sp H Np n s) (hn : n ≠ 12) :
    WP isa j0hash s (J0Mid V sp H (bytesAt s.mem Np n) s.mem) := by
  have hd := h.data
  have hlt := hd.lt
  refine WP.seq (WP.mono (j0zero_ok L h) fun s₁ ⟨hai, hY₁, hiv, f₁⟩ => ?_)
  refine WP.seq (WP.mono (absorb_ok L (yo := 0) (.inl rfl) hai) fun s₂ ho => ?_)
  rw [List.nil_append, hiv] at ho
  have hab₂ := ho.abs (Proof.Gcm.absorbed_nil H hY₁)
  have he₂ := ho.env
  have hH₂ : blockAt s₂.mem (V .r29 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ho.frame (ctx_absFrame L (.inl rfl)), hai.hH]
  have h18 : s₂.gpr .r18 = BitVec.ofNat 64 n := he₂.fr _ (by decide) |>.trans h.r18
  have h₃ : WP isa (.block [.li .r0 15, .logic .and .r26 .r18 .r0]) s₂ fun s₃ =>
      s₃.gpr .r26 = BitVec.ofNat 64 (n % 16) ∧ (∀ r, r ≠ .r0 → r ≠ .r26 → s₃.gpr r = s₂.gpr r) ∧
        Keeps s₂ s₃ := by
    have hand := and15 (BitVec.ofNat 64 n)
    rw [toNat64 hlt] at hand
    crun [h18, hand]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₃ fun s₃ ⟨h26₃, hg₃, hk₃⟩ => ?_)
  have he₃ := he₂.keep (fun r hr => hg₃ r (by revert r; decide) (by revert r; decide)) hk₃.sp hk₃.rd hk₃.wr
  refine WP.seq (WP.mono (flush_ok L (yo := 0) (.inl rfl) (x := bytesAt s.mem Np n) ⟨he₃, by
    rw [hk₃.mem, hH₂]⟩ (by rw [h26₃, length_bytesAt])) fun s₄ hf => ?_)
  have he₄ := hf.env
  have h18₄ : s₄.gpr .r18 = BitVec.ofNat 64 n := he₄.fr _ (by decide) |>.trans h.r18
  have h₅ : WP isa (.block [.li .r24 0, mov .r26 .r18]) s₄ fun s₅ =>
      s₅.gpr .r24 = BitVec.ofNat 64 0 ∧ s₅.gpr .r26 = BitVec.ofNat 64 n ∧
        (∀ r, r ≠ .r24 → r ≠ .r26 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    crun [h18₄, mov, BitVec.or_self]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨h24₅, h26₅, hg₅, hk₅⟩ => ?_)
  have he₅ := he₄.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide)) hk₅.sp hk₅.rd hk₅.wr
  refine WP.mono (lens_ok L (yo := 0) (.inl rfl) (H := H) he₅ (by rw [hk₅.mem]; exact hf.hH))
    fun s₆ ⟨he₆, hH₆, hY₆, _, f₆⟩ => ?_
  refine ⟨he₆, hH₆, ?_, ?_⟩
  · have hw := (hf.abs (by rw [hk₃.mem]; exact hab₂)).whole_eq (by
      simp only [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod n)
    rw [length_bytesAt, add_ofNat_zero] at hw
    rw [h24₅, h26₅, toNat64 (by decide), toNat64 hlt, hk₅.mem, add_ofNat_zero, hw] at hY₆
    rw [Proof.Gcm.j0_eq H (by rw [length_bytesAt]; exact hn), length_bytesAt, ← hY₆]
  · have g₁ : Frame (j0Frame (V .r30) (V .r31)) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    have g₄ := t_j0Frame hf.frame
    have g₆ := t_j0Frame f₆
    rw [hk₃.mem] at g₄
    rw [hk₅.mem] at g₆
    exact ((g₁.trans (abs_j0Frame ho.frame)).trans g₄).trans g₆

omit L in
/-- Branching on `r - k`, for `r` holding `a`. -/
theorem eval_subk {s : State} {r : Reg} {a k : Nat}
    (h : s.gpr r = BitVec.ofNat 64 a - BitVec.ofNat 64 k) (ha : a < 2 ^ 64) (hk : k < 2 ^ 64) :
    isa.eval (.zero .d r) s = some (decide (a = k)) := by
  show some _ = _
  simp only [State.read, Size.bits, BitVec.setWidth_eq, h]
  congr 1
  by_cases hak : a = k
  · subst hak; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 k ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, toNat64 ha, toNat64 hk] at this
      simp at this; omega
    simp only [hak, decide_false, beq_eq_false_iff_ne.mpr this]

/-- `j0`: the streaming state's `J₀`, accumulator and first counter block. -/
theorem j0_ok {H : Block} {Np : Addr} {n : Nat} {s : State} (h : J0In V sp H Np n s) :
    WP isa j0 s (J0Out V sp H (bytesAt s.mem Np n) s.mem) := by
  have hlt := h.data.lt
  have h₁ : WP isa (.block [.subi .r6 .r25 12]) s fun s₁ =>
      s₁.gpr .r6 = BitVec.ofNat 64 n - BitVec.ofNat 64 12 ∧ (∀ r, r ≠ .r6 → s₁.gpr r = s.gpr r) ∧
        Keeps s s₁ := by
    crun [h.r25]
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨h6, hg₁, hk₁⟩ => ?_)
  have hi : J0In V sp H Np n s₁ :=
    ⟨h.env.keep (fun r hr => hg₁ r (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, by rw [hk₁.mem]; exact h.hH,
      by rw [hg₁ _ (by decide)]; exact h.r24, by rw [hg₁ _ (by decide)]; exact h.r25, h.r18,
      h.data.of_eq hk₁.rd hk₁.wr⟩
  rw [← hk₁.mem]
  refine WP.seq (WP.ite (decide (n = 12)) (eval_subk h6 hlt (by decide)) (fun ht => ?_) (fun hf => ?_))
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact WP.mono (j012_ok L hi) fun _ hm => initState_ok L hm
  · exact WP.mono (j0hash_ok L hi (by simpa using hf)) fun _ hm => initState_ok L hm

end

end VG.Proof.AesGcm.PPC64LE
