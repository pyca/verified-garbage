module

public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Flush
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Tag
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesGcm.AArch64.Save
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Impl.AesGcm.AArch64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Cmac.Frame

/-! ### `Sm4Gcm.AArch64.FinTag`, which the modules that import this one used -/

section

/-! ### `Sm4Gcm.AArch64.Body`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.AArch64.J0`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. `j0` writes `J₀` for the
`x24`-byte nonce at `x23` to the state: its bytes and `0x00000001` if it is
12 bytes (`j012_ok`), else GHASH of its whole blocks (`j0Seg_ok`,
`j0Call1_ok`), of its last bytes padded (`padSeg_ok`, `padCall_ok`) and of the
lengths block (`lensSeg_ok`, `lensCall_ok`), `j0hash_ok`; then the first
counter block `inc₃₂(J₀)` and a zero accumulator (`initState_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64 VG.WriteBytes
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

theorem inc32_words (a b c d : BitVec 32) : inc32 (a ++ b ++ c ++ d) = a ++ b ++ c ++ (d + 1) := by
  have h₁ : (a ++ b ++ c ++ d).extractLsb' 32 96 = a ++ b ++ c := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    simp only [show ¬ (32 + i < 32) by omega_using [], ite_false, show 32 + i - 32 = i by omega_using []]
  have h₂ : (a ++ b ++ c ++ d).extractLsb' 0 32 = d := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hi]
  simp only [inc32, h₁, h₂]

theorem ww32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega_using []), Nat.mod_eq_of_lt this]

theorem rev32_eq : AArch64.rev32 = byteRev32 := rfl

theorem le4_one : le4 (BitVec.ofNat 32 0x01000000) = [0, 0, 0, 1] := by decide

/-- A block from the bytes of its four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = byteRev32 a ++ byteRev32 b ++ byteRev32 c ++ byteRev32 d := by
  have h := Proof.Cmac.le4_rev4 (byteRev32 a) (byteRev32 b) (byteRev32 c) (byteRev32 d)
  rw [Proof.Cmac.byteRev32_byteRev32, Proof.Cmac.byteRev32_byteRev32, Proof.Cmac.byteRev32_byteRev32,
    Proof.Cmac.byteRev32_byteRev32] at h
  rw [h, Proof.Cmac.ofBytes_toBytes]

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

/-- `J₀` of a nonce other than 12 bytes, from GHASH of its whole blocks, its
last bytes padded and the lengths block. -/
theorem j0_split (h : Block) (m : Mem) (Np : Addr) {n : Nat} (hn : n ≠ 12) :
    Spec.Gcm.j0 h (bytesAt m Np n) =
      ghashFrom h (ghashFrom h (ghash h (blocks (bytesAt m Np (16 * (n / 16)))))
        (if n % 16 = 0 then [] else
          [ofBytes (bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++ zeros (16 - n % 16))]))
        [ofBytes (lensBlock 0 n)] := by
  rw [Proof.Gcm.j0_eq h (by rw [length_bytesAt]; exact hn), length_bytesAt]
  congr 1
  rw [show bytesAt m Np n = bytesAt m Np (16 * (n / 16)) ++ bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)
      by rw [← bytesAt_add]; congr 1; omega_using [], List.append_assoc,
    Proof.Gcm.blocks_append (by rw [length_bytesAt]; omega_using []), ghash, Proof.Gcm.ghashFrom_append]
  by_cases h0 : n % 16 = 0
  · rw [Proof.Gcm.padLen_of_mod h0]
    simp only [h0, ↓reduceIte]
    rw [show bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) 0 ++ zeros 0 = [] from rfl, Proof.Gcm.blocks_nil]
    rfl
  · simp only [h0, ↓reduceIte]
    rw [show padLen n = 16 - n % 16 by simp only [padLen]; omega_using [h0],
      Proof.Gcm.blocks_single (bs := bytesAt m (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++ zeros (16 - n % 16))
        (by rw [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; omega_using [])]
    rfl

/-- The regions `j0` writes. -/
abbrev j0Frame (St W : Addr) : List Region :=
  [⟨St, 80⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩]

/-- Before `j0`: the `n`-byte nonce at `Np`, its length also in `x26` and 0 in
`x27`. -/
structure J0In (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (Np : Addr) (n : Nat) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = Np
  x24 : s.gpr .x24 = BitVec.ofNat 64 n
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = 0
  data : DataOk St W s Np n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- Before the first call of `j0hash`: a zero accumulator, and the call on the
whole blocks of the nonce. -/
structure J1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (Np : Addr) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = Np + BitVec.ofNat 64 (16 * (n / 16))
  x25 : s.gpr .x25 = BitVec.ofNat 64 (n % 16)
  data : DataOk St W s Np n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  y0 : blockAt s.mem (St + BitVec.ofNat 64 0) = 0
  call : GhCall s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 0) Np (W + BitVec.ofNat 64 512) (n / 16)
  frame : Frame [⟨St, 16⟩] m₀ s.mem

/-- After the first call: the whole blocks absorbed. -/
structure J2 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (Np : Addr) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = Np + BitVec.ofNat 64 (16 * (n / 16))
  x25 : s.gpr .x25 = BitVec.ofNat 64 (n % 16)
  data : DataOk St W s Np n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  y : blockAt s.mem (St + BitVec.ofNat 64 0) = ghash H (blocks (bytesAt m₀ Np (16 * (n / 16))))
  iv : bytesAt s.mem Np n = bytesAt m₀ Np n
  frame : Frame (j0Frame St W) m₀ s.mem

/-- `J₀` written, from `m₀`. -/
structure J0Mid (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  frame : Frame (j0Frame St W) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (Ctx St W SP : Addr) (k : Reg → BitVec 64) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem St = Spec.Gcm.j0 H iv
  y : blockAt s.mem (St + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (j0Frame St W) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨St + BitVec.ofNat 64 d, k⟩] m m') (hk : d + k ≤ 80) :
    Frame (j0Frame St W) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Lay.stSub hk⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (tFrame St W 0) m m') : Frame (j0Frame St W) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- `J₀` of a 12-byte nonce. -/
theorem j012_ok {k : Reg → BitVec 64} {H : Block} {Np : Addr} {s : State} (h : J0In Ctx St W SP k H Np 12 s) :
    WP isa (.block j012) s (J0Mid Ctx St W SP k H (bytesAt s.mem Np 12) s.mem) := by
  have he := h.env
  have hd := h.data
  have r₀ := in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  have r₁ := in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  have r₂ := in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  have w₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  rw [add_ofNat_zero] at r₀ w₀
  obtain ⟨s', run, hm, og, sp, rd, wr⟩ : ∃ s', runBlock isa j012 s = some s' ∧
      s'.mem = store4 s.mem St (s.mem.readW Np 32) (s.mem.readW (Np + BitVec.ofNat 64 4) 32)
        (s.mem.readW (Np + BitVec.ofNat 64 8) 32) (BitVec.ofNat 32 0x01000000) ∧
      Others [.x9, .x10, .x11, .x12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by simp only [j012]; arun [h.x23, he.x20, r₀, r₁, r₂, w₀, w₁, w₂, w₃, add_ofNat_zero], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl⟩
    simp only [mem_write, store4, Mem.writeW, Mem.readW, ww32, BitVec.setWidth_eq]
    rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f : Frame [⟨St + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem := by
    rw [hm, add_ofNat_zero]; exact Proof.Cmac.frame_store4 (m := s.mem) St _ _ _ _
  refine ⟨he.keep (fun r hr => og r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr, h.kept.of_others og, ?_, ?_, st_j0Frame f (by decide)⟩
  · rw [blockAt_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
  · have hb : bytesAt s.mem Np 12 = bytesAt s.mem Np 4 ++ bytesAt s.mem (Np + BitVec.ofNat 64 4) 4 ++
        bytesAt s.mem (Np + BitVec.ofNat 64 8) 4 := by
      rw [show (12 : Nat) = 4 + 8 from rfl, bytesAt_add, show (8 : Nat) = 4 + 4 from rfl, bytesAt_add,
        add_ofNat_assoc, List.append_assoc]
    rw [Proof.Gcm.j0_12 _ (length_bytesAt _ _ _), blockAt, hm, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW,
      Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, le4_one, hb]

/-- The first counter block, and the accumulator zeroed. -/
theorem initState_ok {k : Reg → BitVec 64} {H : Block} {iv : List Byte} {m₀ : Mem} {s : State}
    (h : J0Mid Ctx St W SP k H iv m₀ s) :
    WP isa (.block initState) s (J0Out Ctx St W SP k H iv m₀) := by
  have he := h.env
  have r₀ := he.perm.stR (show 0 + 4 ≤ 80 by decide)
  have r₁ := he.perm.stR (show 4 + 4 ≤ 80 by decide)
  have r₂ := he.perm.stR (show 8 + 4 ≤ 80 by decide)
  have r₃ := he.perm.stR (show 12 + 4 ≤ 80 by decide)
  have w₀ := he.perm.stW (show 48 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 52 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 56 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 60 + 4 ≤ 80 by decide)
  have z₀ := he.perm.stW (show 16 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 24 + 8 ≤ 80 by decide)
  rw [add_ofNat_zero] at r₀
  generalize hw : s.mem.readW (St + BitVec.ofNat 64 12) 32 = w
  obtain ⟨s', run, hm, og, sp, rd, wr⟩ : ∃ s', runBlock isa initState s = some s' ∧
      s'.mem = ((store4 s.mem (St + BitVec.ofNat 64 48) (s.mem.readW St 32) (s.mem.readW (St + BitVec.ofNat 64 4) 32)
        (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1))).writeW (St + BitVec.ofNat 64 16)
          (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 24) (0 : BitVec 64) ∧
      Others [.x9, .x10, .x11, .x12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by simp only [initState]; arun [he.x20, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, z₀, z₁, add_ofNat_zero], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl⟩
    simp only [mem_write, store4, Mem.writeW, Mem.readW, ww32, BitVec.setWidth_eq, ← hw, rev32_eq, add_ofNat_assoc]
    rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f₄ := Proof.Cmac.frame_store4 (m := s.mem) (St + BitVec.ofNat 64 48) (s.mem.readW St 32)
    (s.mem.readW (St + BitVec.ofNat 64 4) 32) (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1))
  have fz := Proof.Cmac.frame_store2 (m := store4 s.mem (St + BitVec.ofNat 64 48) (s.mem.readW St 32)
    (s.mem.readW (St + BitVec.ofNat 64 4) 32) (s.mem.readW (St + BitVec.ofNat 64 8) 32) (byteRev32 (byteRev32 w + 1)))
    (St + BitVec.ofNat 64 16) 0 0
  rw [add_ofNat_assoc, ← hm] at fz
  have dz : (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 16, 16⟩ :=
    L.st_st (.inr (by decide)) (by decide) (by decide)
  have ff : Frame [⟨St + BitVec.ofNat 64 0, 80⟩] s.mem s'.mem := by
    refine (f₄.sub fun r hr => ?_).trans (fz.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hJ : blockAt s'.mem St = blockAt s.mem St := by
    rw [blockAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)),
      blockAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using L.st_st (a := 0) (n := 16) (d := 48) (k := 16) (.inl (by decide)) (by decide) (by decide))]
  refine ⟨he.keep (fun r hr => og r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr, h.kept.of_others og,
    ?_, by rw [hJ, h.j0], ?_, ?_, h.frame.trans (st_j0Frame ff (by decide))⟩
  · rw [blockAt_frame ff (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, hm, show St + BitVec.ofNat 64 24 = St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 by
      rw [add_ofNat_assoc], Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; decide
  · rw [blockAt, bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dz) (by decide),
      Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, ← h.j0, blockAt,
      Proof.Cmac.ofBytes_rev4, ← Proof.Cmac.le4_readW s.mem St, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW,
      ofBytes_le4, hw, Proof.Cmac.byteRev32_byteRev32, inc32_words]

/-- The accumulator zeroed and the arguments for the whole blocks of the
nonce. -/
theorem j0Seg_ok {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : J0In Ctx St W SP k H Np n s) :
    WP isa (.block j0Seg) s (J1 Ctx St W SP k H Np n s.mem) := by
  have he := h.env
  have hd := h.data
  have hlt := hd.lt
  have z₀ := he.perm.stW (show 0 + 8 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 8 + 8 ≤ 80 by decide)
  rw [add_ofNat_zero] at z₀
  obtain ⟨s₁, run₁, hm₁, x3₁, x2₁, x0₁, x1₁, x4₁, x23₁, x25₁, og, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa j0Seg s = some s₁ ∧
      s₁.mem = (s.mem.writeW St (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .x3 = BitVec.ofNat 64 (n / 16) ∧ s₁.gpr .x2 = Np ∧ s₁.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧
      s₁.gpr .x1 = St + BitVec.ofNat 64 0 ∧ s₁.gpr .x4 = W + BitVec.ofNat 64 512 ∧
      s₁.gpr .x23 = Np + BitVec.ofNat 64 (16 * (n / 16)) ∧ s₁.gpr .x25 = BitVec.ofNat 64 (n % 16) ∧
      Others [.x9, .x3, .x2, .x0, .x1, .x4, .x23, .x10, .x25] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by simp only [j0Seg, ghArgs]; arun [he.x20, z₀, z₁, add_ofNat_zero], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq]; rfl
    · simp [gpr_write, h.x24, lsr_ofNat _ _ hlt]
    · simp [gpr_write, h.x23]
    · simp [gpr_write, he.x21]
    · simp [gpr_write, he.x20]
    · simp [gpr_write, he.x19]
    · simp [gpr_write, h.x23, h.x24, lsr_ofNat _ _ hlt, lsl4_ofNat]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h.x24, BitVec.setWidth_eq]
      rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15,
        toNat_ofNat_of_lt hlt]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => og r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have fz : Frame [⟨St, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have hdw := hd.take (k := 16 * (n / 16)) (by omega_using [])
  refine ⟨he₁, h.kept.of_others og, x23₁, x25₁, hd.of_eq rd₁ wr₁, ?_, ?_, ?_, fz⟩
  · rw [blockAt_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.ctx_st (a := 240) (n := 16) (d := 0) (k := 16) (by decide) (by decide), h.hH]
  · rw [add_ofNat_zero, blockAt, hm₁, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; decide
  · exact ghCall_of L (yo := 0) (.inl rfl) he₁ x0₁ x1₁ x2₁ x3₁ x4₁ (by have := hdw.lt; omega_using [hlt])
      (by simpa using (hdw.st.sub_right (Lay.stSub (d := 0) (n := 16) (by decide))).symm)
      (hdw.w.sub_right (Lay.wSub (by decide))) (by rw [rd₁, wr₁]; exact hdw.rd)

/-- The whole blocks of the nonce absorbed. -/
theorem j0Call1_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {m₀ : Mem} {s : State}
    (h : J1 Ctx St W SP k H Np n m₀ s) :
    WP isa (ghCall v.callees) s (J2 Ctx St W SP k H Np n m₀) := by
  have hd := h.data
  refine WP.mono (gh_call v.gh h.call) fun s' g => ?_
  have dD : ∀ r ∈ [(⟨St, 16⟩ : Region)], (⟨Np, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simpa using hd.st.sub_right (Lay.stSub (d := 0) (n := 16) (by decide))
  have dD' : ∀ r ∈ [⟨St + BitVec.ofNat 64 0, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩], (⟨Np, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd.st.sub_right (Lay.stSub (by decide))
    · exact hd.w.sub_right (Lay.wSub (by decide))
  have hiv : bytesAt s.mem Np n = bytesAt m₀ Np n := bytesAt_frame h.frame dD (by have := hd.lt; omega_using [this])
  refine ⟨GhPost.env g h.env, h.kept.of_saved g.saved, by rw [g.saved _ (by decide) (by decide), h.x23],
    by rw [g.saved _ (by decide) (by decide), h.x25], hd.of_eq g.rd g.wr, by rw [hH_gh L (.inl rfl) g, h.hH], ?_,
    by rw [bytesAt_frame g.frame dD' (by have := hd.lt; omega_using [this]), hiv], ?_⟩
  · rw [g.out, h.y0, h.hH, Proof.Gcm.blocksAt_eq]
    have e := congrArg (List.take (16 * (n / 16))) hiv
    rw [bytesAt_take _ _ (by omega_using []), bytesAt_take _ _ (by omega_using [])] at e
    rw [e]; rfl
  · refine (st_j0Frame (W := W) (d := 0) (k := 16) (by simpa using h.frame) (by decide)).trans
      (g.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- `J₀` of a nonce of any length but 12: GHASH of the nonce padded and of
the lengths block. -/
theorem j0hash_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : J0In Ctx St W SP k H Np n s) (hn : n ≠ 12) :
    WP isa (j0hash v.callees) s (J0Mid Ctx St W SP k H (bytesAt s.mem Np n) s.mem) := by
  have hd := h.data
  have hlt := hd.lt
  have k26 : k .x26 = BitVec.ofNat 64 n := by rw [← h.kept .x26 (by decide), h.x26]
  have k27 : k .x27 = 0 := by rw [← h.kept .x27 (by decide), h.x27]
  refine WP.seq (WP.mono (j0Seg_ok L h) fun s₁ h₁ =>
    WP.seq (WP.mono (j0Call1_ok L v h₁) fun s₂ h₂ => ?_))
  have hdr := h₂.data.drop (k := 16 * (n / 16)) (by omega_using [])
  rw [show n - 16 * (n / 16) = n % 16 by omega_using []] at hdr
  refine WP.seq (WP.mono (padSeg_ok L (yo := 0) (.inl rfl) (P := Np + BitVec.ofNat 64 (16 * (n / 16)))
    h₂.env h₂.kept h₂.x25 (Nat.mod_lt _ (by decide))
    (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, h₂.x23], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
    hdr.rd (hdr.w.sub_right (Lay.wSub (by decide)))) fun s₃ h₃ =>
    WP.seq (WP.mono (padCall_ok L (.inl rfl) v h₃) fun s₄ h₄ => ?_))
  refine WP.seq (WP.mono (lensSeg_ok L (yo := 0) (.inl rfl) (ra := .x27) (rb := .x26) h₄.env h₄.kept h₄.x25
    (by decide)) fun s₅ h₅ => WP.mono (lensCall_ok L (.inl rfl) v h₅) fun s₆ h₆ => ?_)
  have a₄ : (s₄.gpr .x27).toNat = 0 := by rw [h₄.kept .x27 (by decide), k27]; rfl
  have b₄ : (s₄.gpr .x26).toNat = n := by rw [h₄.kept .x26 (by decide), k26, toNat_ofNat_of_lt hlt]
  have hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := h₂.hH
  have hH₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame h₄.frame (ctx_tFrame L (.inl rfl)), hH₂]
  have hP : bytesAt s₂.mem (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (Np + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    have e := congrArg (List.drop (16 * (n / 16))) h₂.iv
    rw [bytesAt_drop _ _ (by omega_using []), bytesAt_drop _ _ (by omega_using []), show n - 16 * (n / 16) = n % 16 by omega_using []] at e
    exact e
  refine ⟨h₆.env, h₆.kept, by rw [blockAt_frame h₆.frame (ctx_tFrame L (.inl rfl)), hH₄], ?_, ?_⟩
  · rw [← add_ofNat_zero St, h₆.out, h₄.out, hH₄, hH₂, a₄, b₄, h₂.y, hP, j0_split H s.mem Np hn]
  · exact (h₂.frame.trans (t_j0Frame h₄.frame)).trans (t_j0Frame h₆.frame)

/-- `j0`: the streaming state's `J₀`, accumulator and first counter block. -/
theorem j0_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : J0In Ctx St W SP k H Np n s) :
    WP isa (j0 v.callees) s (J0Out Ctx St W SP k H (bytesAt s.mem Np n) s.mem) := by
  have hlt := h.data.lt
  obtain ⟨s₁, run₁, x9₁, r₁⟩ : ∃ s₁, runBlock isa [.subImm .x .x9 .x24 12] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12 ∧ Regs [.x9] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h.x24], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  have h₁ : J0In Ctx St W SP k H Np n s₁ :=
    ⟨h.env.of_regs r₁, h.kept.of_others r₁.others, by rw [r₁.others _ (by decide)]; exact h.x23,
      by rw [r₁.others _ (by decide)]; exact h.x24, by rw [r₁.others _ (by decide)]; exact h.x26,
      by rw [r₁.others _ (by decide)]; exact h.x27, h.data.of_eq r₁.rd r₁.wr, by rw [r₁.mem]; exact h.hH⟩
  have ev : isa.eval (.zero .x .x9) s₁ = some (decide (n = 12)) := by
    show some (s₁.read .x .x9 == 0) = _
    rw [State.read, x9₁, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat_beq hlt (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  rw [← r₁.mem]
  refine WP.seq (WP.ite (decide (n = 12)) ev (fun ht => ?_) (fun hf => ?_))
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact WP.mono (j012_ok L h₁) fun _ hm => initState_ok L hm
  · exact WP.mono (j0hash_ok L v h₁ (by simpa using hf)) fun _ hm => initState_ok L hm

end

end VG.Proof.Sm4Gcm.AArch64

end

end

/-! ### `Sm4Gcm.AArch64.Save`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: saving and restoring our caller's registers

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/AArch64/Save.lean`, whose definitions and lemmas on the slots
this uses), for SM4-GCM's 768-byte working space.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Proof.AesGcm.AArch64

theorem save_ok (s : State) (b : Reg) {W : Addr} (hb : s.gpr b = W) (hw : Covers [⟨W, 768⟩] s.wr) :
    ∃ s', runBlock isa (save b) s = some s' ∧ s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = savedMem s.mem W s.gpr := by
  have w (d : Nat) (h : d + 8 ≤ 768) : InRegions s.wr (W + BitVec.ofNat 64 d) 8 := in_off hw h (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies, implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, save, saved, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, ite_true, ite_false, Option.bind_some, hb,
      w 128 (by decide), w 136 (by decide), w 144 (by decide), w 152 (by decide), w 160 (by decide),
      w 168 (by decide), w 176 (by decide), w 184 (by decide), w 192 (by decide), w 200 (by decide),
      w 208 (by decide)]
    rfl, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp only [savedMem, saved, List.foldl, Mem.writeW, BitVec.setWidth_eq]

theorem restore_ok (s : State) {W : Addr} (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, 768⟩] (s.rd ++ s.wr)) :
    ∃ s', runBlock isa restore s = some s' ∧
      (∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (W + BitVec.ofNat 64 p.2) 64) ∧
      (∀ r, r ∉ saved.map (·.1) → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have r (d : Nat) (h : d + 8 ≤ 768) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 := in_off hr h (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies, implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write,
      wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, h19,
      r 128 (by decide), r 136 (by decide), r 144 (by decide), r 152 (by decide), r 160 (by decide),
      r 168 (by decide), r 176 (by decide), r 184 (by decide), r 192 (by decide), r 200 (by decide),
      r 208 (by decide)]
    rfl, ?_⟩
  refine ⟨fun p h => ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_write, Mem.readW]
  · simp only [saved, List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp [gpr_write, h]

/-- The end of every function: our caller's registers restored. -/
theorem exit_ok {s s₀ : State} {W : Addr} (h19 : s.gpr .x19 = W) (hsp : s.sp = s₀.sp)
    (hr : Covers [⟨W, 768⟩] (s.rd ++ s.wr)) (hs : SavedAt s.mem W s₀) :
    WP isa (.block restore) s fun s' => GprAbi s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .x0 = s.gpr .x0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', run, hsv, hother, sp', hm, rd', wr'⟩ := restore_ok s h19 hr
  refine WP.of_runBlock ⟨s', run, ⟨fun r hr' => ?_, by rw [sp', hsp]⟩, hm, hother .x0 (by decide), rd', wr'⟩
  have hin : r ∈ saved.map (·.1) := (by decide : ∀ r ∈ preserved, r ∈ saved.map (·.1)) r hr'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hin
  rw [hsv p hp, hs p hp]

end VG.Proof.Sm4Gcm.AArch64

end

end

/-! ### `Sm4Gcm.AArch64.Fn`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: what every function uses

Untrusted: everything here is checked by Lean. The postconditions quantify
over what the state represents (the nonce, the additional data, the text so
far), which the code never looks at: each function runs the same for all of
them, so one run satisfies each instance of its proof (`WP.forall_det`). The
pieces never write the saved registers (`saved_absFrame`, …), and `flush` of
no bytes changes no accumulator (`flush0_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom)

/-- A run that satisfies `R`, and for each `i` with `P i`, `Q i`. -/
theorem WP.forall_det {c : Prog isa} {s : State} {ι : Sort _} {P : ι → Prop} {Q : ι → State → Prop}
    {R : State → Prop} (h₀ : WP isa c s R) (h : ∀ i, P i → WP isa c s (Q i)) :
    WP isa c s fun s' => R s' ∧ ∀ i, P i → Q i s' := by
  obtain ⟨t, s', e, r⟩ := h₀
  refine ⟨t, s', e, r, fun i hi => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h i hi
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-- The layout, from disjointness of the context, the state, `W` and the
stack below `SP`. -/
theorem Lay.of {Ctx St W SP : Addr} (cw : Ctx.toNat + 256 ≤ 2 ^ 64) (sw : St.toNat + 80 ≤ 2 ^ 64)
    (ww : W.toNat + 768 ≤ 2 ^ 64) (cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩)
    (cW : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 768⟩) (sW : (⟨St, 80⟩ : Region).Disjoint ⟨W, 768⟩)
    (sp : 3264 ≤ SP.toNat) (kC : (stk SP).Disjoint ⟨Ctx, 256⟩) (kS : (stk SP).Disjoint ⟨St, 80⟩)
    (kW : (stk SP).Disjoint ⟨W, 768⟩) : Lay Ctx St W SP :=
  ⟨cw, sw, ww, cs, cW, sW.sub_right (Region.sub_prefix (by decide)), sW.sub_right (Lay.wSub (by decide)),
    sp, kC, kS, kW⟩

theorem toNat_mod16 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem saved_absFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ absFrame St W yo, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by omega_using [hyo]) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_tFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ tFrame St W yo, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by omega_using [hyo]) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_tagFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ tagFrame St W SP o, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by omega_using [ho])) (by decide) (by omega_using [ho])
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_j0Frame : ∀ r ∈ j0Frame St W, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W SP s D n) :
    ∀ r ∈ crFrame St SP D n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.stk_w (by decide)).symm

theorem saved_cmp : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)], (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_tag16 : ∀ r ∈ [(⟨W, 16⟩ : Region)], (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  simpa using L.w_w (a := 128) (n := 88) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)

/-- `flush` of no bytes: the accumulator as it was. -/
theorem flush0_ok (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {k : Reg → BitVec 64} {s : State}
    (he : Env Ctx St W SP s) (hk : Kept k s) (h25 : s.gpr .x25 = BitVec.ofNat 64 0) :
    WP isa (flush v.callees yo) s (TOut Ctx St W SP k yo 0 (blockAt s.mem (St + BitVec.ofNat 64 yo)) s.mem) := by
  refine WP.seq (WP.mono (padSeg_ok L hyo (P := St + BitVec.ofNat 64 32) he hk h25 (by decide)
    (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, he.x20], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
    (covers_left (he.perm.stC (by omega_using []))) (L.st_w (by omega_using []) (.inr ⟨by decide, by decide⟩))) fun s₁ h₁ => ?_)
  refine WP.mono (padCall_ok L hyo v h₁) fun s₂ h₂ => { h₂ with out := ?_ }
  rw [h₂.out]; rfl

end

end VG.Proof.Sm4Gcm.AArch64

end

end

/-! ### `Sm4Gcm.AArch64.Text`, which only this module used -/

section

/-!
# SM4-GCM on AArch64: the additional data padded before the first text

Untrusted: everything here is checked by Lean. `fo` leaves the number of
buffered bytes of additional data in `x25` if this is the first text (and
there is text), and 0 otherwise (`fo_ok`); `flush` then pads and absorbs
them, or changes nothing GHASH has absorbed (`flushStep_ok`): GHASH has then
absorbed `xf a c n`, which the text continues (`ghashInput_xf`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- What GHASH has absorbed before `n` more bytes of text: the additional data
padded if this is the first text. -/
def xf (a c : List Byte) (n : Nat) : List Byte :=
  if n ≠ 0 ∧ c = [] then a ++ zeros (padLen a.length) else ghashInput a c

theorem xf_len {a c : List Byte} {n : Nat} (hn : n ≠ 0) : (xf a c n).length % 16 = c.length % 16 := by
  unfold xf
  by_cases hc : c = []
  · subst hc
    simp only [ne_eq, hn, not_false_eq_true, true_and, ↓reduceIte, List.length_append, Proof.Gcm.length_zeros,
      List.length_nil]
    exact Proof.Gcm.length_pad_mod _
  · simp only [hc, and_false, ↓reduceIte, Proof.Gcm.ghashInput_of_ne hc, List.length_append,
      Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega_using [this]

theorem ghashInput_xf (a c e : List Byte) : ghashInput a (c ++ e) = xf a c e.length ++ e := by
  by_cases he : e = []
  · subst he; simp [xf]
  · have hl : e.length ≠ 0 := fun h => he (List.eq_nil_of_length_eq_zero h)
    rw [Proof.Gcm.ghashInput_append _ _ _ he, xf]
    by_cases hc : c = [] <;> simp [hc, hl]

/-- `fo`: the bytes to pad, if this is the first text. -/
theorem fo_ok {s : State} {q n P : Nat} (h25 : s.gpr .x25 = BitVec.ofNat 64 q)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 n) (h27 : s.gpr .x27 = BitVec.ofNat 64 P) (hn : n < 2 ^ 64)
    (hP : P < 2 ^ 64) :
    WP isa fo s fun s' => s'.gpr .x25 = BitVec.ofNat 64 (if n ≠ 0 ∧ P = 0 then q else 0) ∧ Regs [.x25] s s' := by
  refine WP.ite (decide (n = 0)) (eval_zero h26 hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'; exact ⟨by simp [gpr_write, h0], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.ite (decide (P = 0)) (eval_zero h27 hP) (fun ht' => ?_) (fun hf' => ?_)
    · have h1 : P = 0 := by simpa using ht'
      exact WP.block_nil ⟨by simp [h25, h0, h1], Regs.refl _ _⟩
    · have h1 : P ≠ 0 := by simpa using hf'
      exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
        subst hs'; exact ⟨by simp [gpr_write, h1], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `flush` after `fo`: GHASH has absorbed `xf a c n`, where it had absorbed
`ghashInput a c`. -/
theorem flushStep_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {s : State} {a c : List Byte} {n : Nat}
    (he : Env Ctx St W SP s) (hk : Kept k s)
    (h25 : s.gpr .x25 = BitVec.ofNat 64 (if n ≠ 0 ∧ c.length = 0 then a.length % 16 else 0))
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (flush v.callees 16) s fun s' => Env Ctx St W SP s' ∧ Kept k s' ∧
      blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = H ∧ Frame (tFrame St W 16) s.mem s'.mem ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (xf a c n)) := by
  by_cases hf : n ≠ 0 ∧ c.length = 0
  · have hc : c = [] := List.eq_nil_of_length_eq_zero hf.2
    subst hc
    rw [ite_eq_left hf] at h25
    refine WP.mono (flush_ok L (.inr rfl) v (x := a) he hk h25 rfl hH) fun s' ⟨ho, hH', habs⟩ =>
      ⟨ho.env, ho.kept, hH', ho.frame, fun ha => ?_⟩
    rw [xf, ite_eq_left ⟨hf.1, rfl⟩]
    exact habs ha
  · rw [ite_eq_right hf] at h25
    refine WP.mono (flush0_ok L v (.inr rfl) he hk h25) fun s' ho =>
      ⟨ho.env, ho.kept, by rw [blockAt_frame ho.frame (ctx_tFrame L (.inr rfl)), hH], ho.frame, fun ha => ?_⟩
    have hx : xf a c n = ghashInput a c := by
      rw [xf, ite_eq_right]; intro h; exact hf ⟨h.1, by rw [h.2]; rfl⟩
    rw [hx]
    refine ha.congr ho.out ?_
    refine bytesAt_frame ho.frame (fun r hr => ?_) (by omega_using [])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hl : (ghashInput a c).length % 16 < 16 := Nat.mod_lt _ (by decide)
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (.inr (by omega_using [])) (by have := L.sw; omega_using []) (by have := L.sw; omega_using [])
    · exact L.st_w (by omega_using []) (.inr ⟨by decide, by decide⟩)
    · exact L.st_w (by omega_using []) (.inr ⟨by decide, by decide⟩)

end

end VG.Proof.Sm4Gcm.AArch64

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.Gcm (Absorbed Ctr)

/-- GHASH's accumulator and buffer stay as they are, outside a frame. -/
theorem Absorbed.frame {m m' : Mem} {St : Addr} {H : Block} {x : List Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r)
    (ha : Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H x) :
    Absorbed m' (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H x := by
  have hl : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
  exact ha.congr (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by omega_using [])))
    (bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_using []) (by omega_using []))) (by omega_using []))

/-- The counter block and the keystream block stay as they are, outside a frame. -/
theorem Ctr.frame {m m' : Mem} {St : Addr} {ciph : Block → Block} {icb : Block} {n : Nat} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r)
    (hc : Ctr m (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) ciph icb n) :
    Ctr m' (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) ciph icb n :=
  hc.congr (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by omega_using [])))
    (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_using []) (by omega_using [])))

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- Parts of the state apart from a part of `W`. -/
theorem st_wpart {d k e j : Nat} (hd : d + k ≤ 80) (he : 96 ≤ e ∧ e + j ≤ 768) :
    (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
  L.st_w hd (.inr he)

theorem st_st' {d k e j : Nat} (h : d + k ≤ e ∨ e + j ≤ d) (hd : d + k ≤ 80) (he : e + j ≤ 80) :
    (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 e, j⟩ :=
  L.st_st h hd he

theorem st0_disj {e j : Nat} (h : 16 ≤ e) (he : e + j ≤ 80) :
    (⟨St, 16⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 e, j⟩ := by
  simpa using L.st_st (a := 0) (n := 16) (d := e) (k := j) (.inl h) (by decide) he

theorem st0_w {e j : Nat} (he : 96 ≤ e ∧ e + j ≤ 768) :
    (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ := by
  simpa using L.st_w (a := 0) (n := 16) (d := e) (k := j) (by decide) (.inr he)

theorem st0_saved : (⟨St, 16⟩ : Region).Disjoint (savedR W) := st0_w L ⟨by decide, by decide⟩

end

end VG.Proof.Sm4Gcm.AArch64

end

end


/-!
# SM4-GCM on AArch64: the bodies of `encrypt` and `decrypt`

Untrusted: everything here is checked by Lean. With the additional data `a`
and the ciphertext `c` so far, of `P` bytes, and `n` bytes at `D`: the
additional data padded if this is the first text (`fo`, `flush`), then the
data encrypted and the ciphertext absorbed (`encBody_ok`), or the data
absorbed and decrypted (`decBody_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- Code never changes the permissions or the stack pointer. -/
theorem WP.with_rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', e, q⟩ := h; exact ⟨t, s', e, q, (Exec.rdwr e).1, (Exec.rdwr e).2.1⟩

theorem WP.seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨t, s', e, q⟩ := h
  cases e with
  | seq e₁ e₂ => cases e₁ with
    | seq ea eb => exact ⟨_, _, .seq ea (.seq eb e₂), q⟩

/-- The regions the bodies write. -/
abbrev bodyFrame (St W SP D : Addr) (n : Nat) : List Region :=
  tFrame St W 16 ++ crFrame St SP D n ++ absFrame St W 16

/-- Before a body. -/
structure BodyIn (Ctx St W SP : Addr) (k : Reg → BitVec 64) (n P : Nat) (D : Addr) (a c : List Byte)
    (H : Block) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  x25 : s.gpr .x25 = BitVec.ofNat 64 (a.length % 16)
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = BitVec.ofNat 64 P
  x28 : s.gpr .x28 = D
  hc : c.length = P
  hP : P < 2 ^ 64
  data : DataW Ctx St W SP s D n
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H

/-- What a body leaves, from `m₀`, where `e` is the data absorbed and `out`
what it leaves at `D`. -/
structure BodyOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (n P : Nat) (D : Addr) (a c : List Byte)
    (H : Block) (icb : Block) (e out : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  frame : Frame (bodyFrame St W SP D n) m₀ s.mem
  post : Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
    Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb P →
    Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a (c ++ e)) ∧
      Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb (P + n) ∧
      bytesAt s.mem D n = out

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem ctx_tFrame' : ∀ r ∈ tFrame St W 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))

theorem ctx_absFrame' : ∀ r ∈ absFrame St W 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))

theorem acc_tFrame_free : ∀ r ∈ tFrame St W 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact st_st' L (.inr (by decide)) (by decide) (by decide)
  · exact st_wpart L (by decide) ⟨by decide, by decide⟩
  · exact st_wpart L (by decide) ⟨by decide, by decide⟩

theorem ctr_absFrame : ∀ r ∈ absFrame St W 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact st_st' L (.inr (by decide)) (by decide) (by decide)
  · exact st_st' L (.inr (by decide)) (by decide) (by decide)
  · exact st_wpart L (by decide) ⟨by decide, by decide⟩

theorem acc_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W SP s D n) :
    ∀ r ∈ crFrame St SP D n, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.st.sub_right (Lay.stSub (by decide))).symm
  · exact st_st' L (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_st (by decide)).symm

omit L in
theorem data_tFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W SP s D n) :
    ∀ r ∈ tFrame St W 16, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.ok.st.sub_right (Lay.stSub (by decide))
  · exact hd.ok.w.sub_right (Lay.wSub (by decide))
  · exact hd.ok.w.sub_right (Lay.wSub (by decide))

theorem hH_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W SP s D n) {m m' : Mem}
    (hf : Frame (crFrame St SP D n) m m') :
    blockAt m' (Ctx + BitVec.ofNat 64 240) = blockAt m (Ctx + BitVec.ofNat 64 240) :=
  blockAt_frame hf fun r hr => (ctx_crFrame L hd r hr).sub_left (Lay.ctxSub (by decide))

/-- The additional data padded if this is the first text: `fo` and `flush`. -/
theorem pad_ok (v : GcmImpl) {k : Reg → BitVec 64} {n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : BodyIn Ctx St W SP k n P D a c H s) :
    WP isa (.seq fo (flush v.callees 16)) s fun s' => Env Ctx St W SP s' ∧ Kept k s' ∧
      blockAt s'.mem (Ctx + BitVec.ofNat 64 240) = H ∧ Frame (tFrame St W 16) s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (xf a c n)) := by
  have hn := h.data.ok.lt
  refine WP.seq (WP.mono (fo_ok h.x25 h.x26 h.x27 hn h.hP) fun s₁ ⟨x25₁, r₁⟩ => ?_)
  have he₁ := h.env.of_regs r₁
  have h25 : s₁.gpr .x25 = BitVec.ofNat 64 (if n ≠ 0 ∧ c.length = 0 then a.length % 16 else 0) := by
    rw [x25₁, h.hc]
  refine WP.mono (WP.with_rdwr (flushStep_ok L v he₁ (h.kept.of_others r₁.others) h25
    (by rw [r₁.mem]; exact h.hH))) fun s₂ ⟨⟨he₂, hk₂, hH₂, f₂, abs₂⟩, rd₂, wr₂⟩ =>
    ⟨he₂, hk₂, hH₂, by rw [← r₁.mem]; exact f₂, by rw [rd₂, r₁.rd], by rw [wr₂, r₁.wr],
      fun ha => abs₂ (by rw [r₁.mem]; exact ha)⟩

omit L in
/-- `textArgs`: the offset into the text, and the text as the piece. -/
theorem textArgs_ok {k : Reg → BitVec 64} {n P : Nat} {D : Addr} {s : State} (hk : Kept k s)
    (k26 : k .x26 = BitVec.ofNat 64 n) (k27 : k .x27 = BitVec.ofNat 64 P) (k28 : k .x28 = D) (hP : P < 2 ^ 64) :
    WP isa (.block textArgs) s fun s' => s'.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧ s'.gpr .x23 = D ∧
      s'.gpr .x24 = BitVec.ofNat 64 n ∧ Regs [.x9, .x25, .x23, .x24] s s' := by
  have h26 := (hk .x26 (by decide)).trans k26
  have h27 := (hk .x27 (by decide)).trans k27
  have h28 := (hk .x28 (by decide)).trans k28
  refine WP.run ⟨_, by simp only [textArgs]; arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, by simp [gpr_write, h28], by simp [gpr_write, h26], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h27, BitVec.setWidth_eq]
  rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15,
    toNat_ofNat_of_lt hP]

omit L in
/-- `mov x23, x28; mov x24, x26`. -/
theorem textPiece_ok {k : Reg → BitVec 64} {n : Nat} {D : Addr} {s : State} (hk : Kept k s)
    (k26 : k .x26 = BitVec.ofNat 64 n) (k28 : k .x28 = D) :
    WP isa (.block [mov .x23 .x28, mov .x24 .x26]) s fun s' => s'.gpr .x23 = D ∧
      s'.gpr .x24 = BitVec.ofNat 64 n ∧ Regs [.x23, .x24] s s' := by
  have h26 := (hk .x26 (by decide)).trans k26
  have h28 := (hk .x28 (by decide)).trans k28
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  exact ⟨by simp [gpr_write, h28], by simp [gpr_write, h26], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩

omit L in
theorem mem_bt {St W D : Addr} {n : Nat} {r : Region} (h : r ∈ tFrame St W 16) : r ∈ bodyFrame St W SP D n :=
  List.mem_append_left _ (List.mem_append_left _ h)

omit L in
theorem mem_bc {St W D : Addr} {n : Nat} {r : Region} (h : r ∈ crFrame St SP D n) : r ∈ bodyFrame St W SP D n :=
  List.mem_append_left _ (List.mem_append_right _ h)

omit L in
theorem mem_ba {St W D : Addr} {n : Nat} {r : Region} (h : r ∈ absFrame St W 16) : r ∈ bodyFrame St W SP D n :=
  List.mem_append_right _ h

/-- `encBody`: the data encrypted, and the ciphertext absorbed. -/
theorem encBody_ok (v : GcmImpl) {k : Reg → BitVec 64} {n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : BodyIn Ctx St W SP k n P D a c H s) (icb : Block) :
    WP isa (encBody v.callees) s (BodyOut Ctx St W SP k n P D a c H icb
      (xorKs (ciphOf s.mem Ctx) icb P (bytesAt s.mem D n))
      (xorKs (ciphOf s.mem Ctx) icb P (bytesAt s.mem D n)) s.mem) := by
  have k26 : k .x26 = BitVec.ofNat 64 n := (h.kept .x26 (by decide)).symm.trans h.x26
  have k27 : k .x27 = BitVec.ofNat 64 P := (h.kept .x27 (by decide)).symm.trans h.x27
  have k28 : k .x28 = D := (h.kept .x28 (by decide)).symm.trans h.x28
  have hlt := h.data.ok.lt
  refine WP.seq_assoc (WP.seq (WP.mono (pad_ok L v h) fun s₂ ⟨he₂, hk₂, hH₂, f₂, rd₂, wr₂, abs₂⟩ => ?_))
  refine WP.seq (WP.mono (textArgs_ok hk₂ k26 k27 k28 h.hP) fun s₃ ⟨x25₃, x23₃, x24₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have hd₃ : DataW Ctx St W SP s₃ D n := h.data.of_eq (by rw [r₃.rd, rd₂]) (by rw [r₃.wr, wr₂])
  have hCr : CrIn Ctx St W SP k P D n s₃ :=
    ⟨he₃, hk₃, x23₃, x24₃, x25₃, hd₃⟩
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L v (icb := icb) hCr)) fun s₄ ⟨h₄, rd₄, wr₄⟩ => ?_)
  refine WP.seq (WP.mono (textPiece_ok h₄.kept k26 k28) fun s₅ ⟨x23₅, x24₅, r₅⟩ => ?_)
  have he₅ := h₄.env.of_regs r₅
  have hk₅ := h₄.kept.of_others r₅.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have hc₃ : ciphOf s₃.mem Ctx = ciphOf s.mem Ctx := by
    rw [m₃]; exact ciph_frame f₂ (ctx_tFrame' L)
  have hD₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [m₃]; exact bytesAt_frame f₂ (data_tFrame h.data) (by omega_arith)
  have F₅ : Frame (bodyFrame St W SP D n) s.mem s₅.mem := by
    rw [r₅.mem]
    exact (f₂.sub fun r hr => ⟨r, mem_bt hr, fun _ h => h⟩).trans
      (by rw [← m₃]; exact h₄.frame.sub fun r hr => ⟨r, mem_bc hr, fun _ h => h⟩)
  have hC₃ : ∀ hctr : Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx) icb P,
      Ctr s₃.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₃.mem Ctx) icb P := fun hctr => by
    rw [hc₃, m₃]; exact Ctr.frame f₂ (acc_tFrame_free L) hctr
  have hA₅ : ∀ ha : Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c),
      Absorbed s₅.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (xf a c n) := fun ha => by
    rw [r₅.mem]; exact Absorbed.frame h₄.frame (acc_crFrame L hd₃) (by rw [m₃]; exact abs₂ ha)
  have hO₅ : ∀ hctr : Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx) icb P,
      bytesAt s₅.mem D n = xorKs (ciphOf s.mem Ctx) icb P (bytesAt s.mem D n) := fun hctr => by
    rw [r₅.mem, h₄.out (hC₃ hctr), hc₃, hD₃]
  have hK₅ : ∀ hctr : Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx) icb P,
      Ctr s₅.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s.mem Ctx) icb (P + n) :=
    fun hctr => by rw [r₅.mem, ← hc₃]; exact h₄.ctr (hC₃ hctr)
  have hlen : (xorKs (ciphOf s.mem Ctx) icb P (bytesAt s.mem D n)).length = n := by
    rw [Proof.Gcm.length_xorKs, length_bytesAt]
  refine WP.ite (decide (n = 0)) (eval_zero ((hk₅ .x26 (by decide)).trans k26) hlt) (fun ht => ?_) (fun hf => ?_)
  · have hn0 : n = 0 := by simpa using ht
    refine WP.block_nil ⟨he₅, hk₅, F₅, fun ha hctr => ⟨?_, hK₅ hctr, hO₅ hctr⟩⟩
    rw [ghashInput_xf, hlen, hn0, show bytesAt s.mem D 0 = [] from rfl, Proof.Gcm.xorKs_nil, List.append_nil]
    have := hA₅ ha
    rw [hn0] at this
    exact this
  · have hn0 : n ≠ 0 := by simpa using hf
    have hA : AbsIn Ctx St W SP k H (xf a c n) D n (P % 16) s₅ :=
      ⟨he₅, hk₅, x23₅, x24₅, by rw [r₅.others _ (by decide), h₄.x25], by rw [xf_len hn0, h.hc],
        h.data.ok.of_eq (by rw [r₅.rd, rd₄, r₃.rd, rd₂]) (by rw [r₅.wr, wr₄, r₃.wr, wr₂]),
        by rw [r₅.mem, hH_crFrame L hd₃ h₄.frame, m₃, hH₂]⟩
    refine WP.mono (absorb_ok L (.inr rfl) v hA) fun s₆ h₆ => ⟨h₆.env, h₆.kept,
      F₅.trans (h₆.frame.sub fun r hr => ⟨r, mem_ba hr, fun _ h => h⟩), fun ha hctr => ⟨?_, ?_, ?_⟩⟩
    · rw [ghashInput_xf, hlen, ← hO₅ hctr]; exact h₆.abs (hA₅ ha)
    · exact Ctr.frame h₆.frame (ctr_absFrame L) (hK₅ hctr)
    · rw [bytesAt_frame h₆.frame (data_absFrame (.inr rfl) hA.data) (by omega_arith), hO₅ hctr]

/-- `decBody`: the data absorbed, and decrypted. -/
theorem decBody_ok (v : GcmImpl) {k : Reg → BitVec 64} {n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : BodyIn Ctx St W SP k n P D a c H s) (icb : Block) :
    WP isa (decBody v.callees) s (BodyOut Ctx St W SP k n P D a c H icb (bytesAt s.mem D n)
      (xorKs (ciphOf s.mem Ctx) icb P (bytesAt s.mem D n)) s.mem) := by
  have k26 : k .x26 = BitVec.ofNat 64 n := (h.kept .x26 (by decide)).symm.trans h.x26
  have k27 : k .x27 = BitVec.ofNat 64 P := (h.kept .x27 (by decide)).symm.trans h.x27
  have k28 : k .x28 = D := (h.kept .x28 (by decide)).symm.trans h.x28
  have hlt := h.data.ok.lt
  refine WP.seq (WP.seq_assoc (WP.seq (WP.mono (pad_ok L v h) fun s₂ ⟨he₂, hk₂, hH₂, f₂, rd₂, wr₂, abs₂⟩ => ?_)))
  refine WP.seq (WP.mono (textArgs_ok hk₂ k26 k27 k28 h.hP) fun s₃ ⟨x25₃, x23₃, x24₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have hD₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [m₃]; exact bytesAt_frame f₂ (data_tFrame h.data) (by omega_arith)
  have hd₃ : DataW Ctx St W SP s₃ D n := h.data.of_eq (by rw [r₃.rd, rd₂]) (by rw [r₃.wr, wr₂])
  -- After the text is absorbed.
  have mid : WP isa (textAbs v.callees) s₃ fun s₄ => Env Ctx St W SP s₄ ∧ Kept k s₄ ∧
      s₄.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧ Frame (tFrame St W 16 ++ absFrame St W 16) s.mem s₄.mem ∧
      s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s₄.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c ++ bytesAt s.mem D n))) := by
    have F₃ : Frame (tFrame St W 16 ++ absFrame St W 16) s.mem s₃.mem := by
      rw [m₃]; exact f₂.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    refine WP.ite (decide (n = 0)) (eval_zero ((hk₃ .x26 (by decide)).trans k26) hlt) (fun ht => ?_) (fun hf => ?_)
    · have hn0 : n = 0 := by simpa using ht
      refine WP.block_nil ⟨he₃, hk₃, x25₃, F₃, by rw [r₃.rd, rd₂], by rw [r₃.wr, wr₂], fun ha => ?_⟩
      rw [ghashInput_xf, length_bytesAt, hn0, show bytesAt s.mem D 0 = [] from rfl, List.append_nil, m₃]
      have := abs₂ ha
      rw [hn0] at this
      exact this
    · have hn0 : n ≠ 0 := by simpa using hf
      have hA : AbsIn Ctx St W SP k H (xf a c n) D n (P % 16) s₃ :=
        ⟨he₃, hk₃, x23₃, x24₃, x25₃, by rw [xf_len hn0, h.hc], hd₃.ok, by rw [m₃, hH₂]⟩
      refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) v hA)) fun s₄ ⟨h₄, rd₄, wr₄⟩ =>
        ⟨h₄.env, h₄.kept, h₄.x25,
          F₃.trans (h₄.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩),
          by rw [rd₄, r₃.rd, rd₂], by rw [wr₄, r₃.wr, wr₂], fun ha => ?_⟩
      rw [ghashInput_xf, length_bytesAt, ← hD₃]
      exact h₄.abs (by rw [m₃]; exact abs₂ ha)
  refine WP.mono mid fun s₄ ⟨he₄, hk₄, x25₄, F₄, rd₄, wr₄, abs₄⟩ => ?_
  refine WP.seq (WP.mono (textPiece_ok hk₄ k26 k28) fun s₅ ⟨x23₅, x24₅, r₅⟩ => ?_)
  have he₅ := he₄.of_regs r₅
  have hk₅ := hk₄.of_others r₅.others
  have hd₅ : DataW Ctx St W SP s₅ D n := h.data.of_eq (by rw [r₅.rd, rd₄]) (by rw [r₅.wr, wr₄])
  have hCr : CrIn Ctx St W SP k P D n s₅ :=
    ⟨he₅, hk₅, x23₅, x24₅,
      by rw [r₅.others _ (by decide), x25₄], hd₅⟩
  have ctxF : ∀ r ∈ tFrame St W 16 ++ absFrame St W 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ctx_tFrame' L r hr
    · exact ctx_absFrame' L r hr
  have hc₅ : ciphOf s₅.mem Ctx = ciphOf s.mem Ctx := by
    rw [r₅.mem]; exact ciph_frame F₄ ctxF
  have hD₅ : bytesAt s₅.mem D n = bytesAt s.mem D n := by
    rw [r₅.mem]
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega_arith)
    rcases List.mem_append.mp hr with hr | hr
    · exact data_tFrame h.data r hr
    · exact data_absFrame (.inr rfl) h.data.ok r hr
  refine WP.mono (crypt_ok L v (icb := icb) hCr) fun s₆ h₆ => ⟨h₆.env, h₆.kept, ?_, fun ha hctr => ⟨?_, ?_, ?_⟩⟩
  · rw [r₅.mem] at h₆
    exact (F₄.sub fun r hr => ⟨r, by
      rcases List.mem_append.mp hr with hr | hr
      · exact mem_bt hr
      · exact mem_ba hr, fun _ h => h⟩).trans (h₆.frame.sub fun r hr => ⟨r, mem_bc hr, fun _ h => h⟩)
  · rw [r₅.mem] at h₆
    exact Absorbed.frame h₆.frame (acc_crFrame L hd₅) (abs₄ ha)
  · have hC : Ctr s₅.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₅.mem Ctx) icb P := by
      rw [hc₅, r₅.mem]
      refine Ctr.frame F₄ (fun r hr => ?_) hctr
      rcases List.mem_append.mp hr with hr | hr
      · exact acc_tFrame_free L r hr
      · exact ctr_absFrame L r hr
    have := h₆.ctr hC
    rw [hc₅] at this
    exact this
  · have hC : Ctr s₅.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₅.mem Ctx) icb P := by
      rw [hc₅, r₅.mem]
      refine Ctr.frame F₄ (fun r hr => ?_) hctr
      rcases List.mem_append.mp hr with hr | hr
      · exact acc_tFrame_free L r hr
      · exact ctr_absFrame L r hr
    rw [h₆.out hC, hc₅, hD₅]

end

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: the tag of a whole message (`finBody`)

Untrusted: everything here is checked by Lean. `finBody o` pads and absorbs
the buffered bytes (of the text, or of the additional data if there is no
text), and writes `GHASH(…, lengths) ⊕ CIPH_K(J₀)` to `W + o`: the tag of the
message (`finBody_ok`, `Proof.Gcm.fullTag_eq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput zeros padLen ofBytes toBytes)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem lensBlock_mod_left (a c : Nat) : lensBlock (a % 2 ^ 64) c = lensBlock a c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (a % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * a)]
  congr 2; omega_using []

/-- The buffered bytes: of the additional data if there is no text. -/
theorem ghashInput_mod {a c : List Byte} : (ghashInput a c).length % 16 =
    if c.length = 0 then a.length % 16 else c.length % 16 := by
  by_cases hc : c = []
  · subst hc; rfl
  · have hl : c.length ≠ 0 := fun h => hc (List.eq_nil_of_length_eq_zero h)
    rw [Proof.Gcm.ghashInput_of_ne hc, ite_eq_right hl]
    simp only [List.length_append, Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega_using [this]

/-- The regions `finBody o` writes. -/
abbrev finFrame (St W SP : Addr) (o : Nat) : List Region := tFrame St W 16 ++ tagFrame St W SP o

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
/-- The offset of the buffered bytes. -/
theorem finOff_ok {s : State} {A P : Nat} (h26 : s.gpr .x26 = BitVec.ofNat 64 A)
    (h27 : s.gpr .x27 = BitVec.ofNat 64 P) (hA : A < 2 ^ 64) (hP : P < 2 ^ 64) :
    WP isa (.ite (.zero .x .x27) (.block [imm .x9 15, .logic .and .x .x25 .x26 .x9])
      (.block [imm .x9 15, .logic .and .x .x25 .x27 .x9])) s fun s' =>
      s'.gpr .x25 = BitVec.ofNat 64 (if P = 0 then A % 16 else P % 16) ∧ Regs [.x9, .x25] s s' := by
  refine WP.ite (decide (P = 0)) (eval_zero h27 hP) (fun ht => ?_) (fun hf => ?_)
  · have h0 : P = 0 := by simpa using ht
    refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h26, BitVec.setWidth_eq, h0]
    rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hA]
  · have h0 : P ≠ 0 := by simpa using hf
    refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h27, BitVec.setWidth_eq, h0]
    rw [show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hP]

/-- `finBody o`: the tag of the message `a`, `c` into `W + o`. -/
theorem finBody_ok (v : GcmImpl) {o : Nat} (ho : o = 0 ∨ o = 112) {k : Reg → BitVec 64}
    {a c : List Byte} {H : Block} {s : State} (he : Env Ctx St W SP s) (hk : Kept k s)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 a.length) (h27 : s.gpr .x27 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) :
    WP isa (finBody v.callees o) s fun s' => Env Ctx St W SP s' ∧ Kept k s' ∧
      Frame (finFrame St W SP o) s.mem s'.mem ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        bytesAt s'.mem (W + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom H (ghash H (blocks (padded a c))) [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem Ctx (blockAt s.mem St))) := by
  have hA : a.length % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have h26' : s.gpr .x26 = BitVec.ofNat 64 (a.length % 2 ^ 64) := by rw [h26]; apply BitVec.eq_of_toNat_eq; simp
  refine WP.seq (WP.mono (finOff_ok h26' h27 hA hc) fun s₁ ⟨x25₁, r₁⟩ => ?_)
  have he₁ := he.of_regs r₁
  have hk₁ := hk.of_others r₁.others
  have h25 : s₁.gpr .x25 = BitVec.ofNat 64 ((ghashInput a c).length % 16) := by
    rw [x25₁, ghashInput_mod]
    by_cases h0 : c.length = 0
    · rw [ite_eq_left h0, ite_eq_left h0, Nat.mod_mod_of_dvd _ (by decide)]
    · rw [ite_eq_right h0, ite_eq_right h0]
  refine WP.seq (WP.mono (flush_ok L (.inr rfl) v (H := H) (x := ghashInput a c) he₁ hk₁ h25 rfl
    (by rw [r₁.mem]; exact hH)) fun s₂ ⟨h₂, hH₂, abs₂⟩ => ?_)
  refine WP.mono (tag_ok L v ho h₂.env h₂.kept h₂.x25) fun s₃ h₃ => ⟨h₃.env, h₃.kept, ?_, fun ha => ?_⟩
  · rw [← r₁.mem]
    exact (h₂.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (h₃.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  · have f₂ := h₂.frame
    rw [r₁.mem] at f₂ abs₂
    have hacc := Proof.Gcm.Absorbed.whole_eq (abs₂ ha) (Proof.Gcm.length_padded a c)
    rw [h₃.out, hH₂, hacc]
    have h26₂ : (s₂.gpr .x26).toNat = a.length % 2 ^ 64 := by
      rw [h₂.kept .x26 (by decide), ← hk .x26 (by decide), h26', toNat_ofNat_of_lt hA]
    have h27₂ : (s₂.gpr .x27).toNat = c.length := by
      rw [h₂.kept .x27 (by decide), ← hk .x27 (by decide), h27, toNat_ofNat_of_lt hc]
    rw [h26₂, h27₂, lensBlock_mod_left, ciph_frame f₂ (ctx_tFrame' L),
      blockAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact st0_disj L (by decide) (by decide)
        · exact st0_w L ⟨by decide, by decide⟩
        · exact st0_w L ⟨by decide, by decide⟩)]
    rfl

theorem saved_finFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ finFrame St W SP o, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact saved_tFrame L (.inr rfl) r hr
  · exact saved_tagFrame L ho r hr


end

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Sm4/Gcm/Contract.lean`, which imply these
(`Verified.lean`). As AES-GCM's (`Proof/AesGcm/AArch64/Contract.lean`), but
with the 3264 bytes of stack below the stack pointer that the callees use
(`stk`), apart from every buffer; `seal` and `open` read their last
arguments from the stack, which they may only read.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr gctr inc32 j0 fullTag tagLenOk encryptWith openResult)
open VG.Spec.Sm4.Gcm (KeyRepr ctxCiph)
open VG.Spec.Gcm (ctxH)

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

/-- `vg_sm4_gcm_init(key = x0, ctx = x1, scratch = x2)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 16⟩
    let ctx : Region := ⟨s.gpr .x1, 256⟩
    let scr : Region := ⟨s.gpr .x2, 768⟩
    3264 ≤ s.sp.toNat ∧ s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (stk s.sp).Disjoint key ∧ (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint scr ∧
      (s.gpr .x0).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 768 ≤ 2 ^ 64
  post s s' := KeyRepr s'.mem (s.gpr .x1) (bytesAt s.mem (s.gpr .x0) 16)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- What `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` need:
`(ctx = x0, state = x1, aad_len = x2, text_len = x3, data = x4, len = x5, scratch = x6)`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x1, 80⟩
  let data : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let scr : Region := ⟨s.gpr .x6, 768⟩
  3264 ≤ s.sp.toNat ∧ s.rd = [ctx] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ data.Disjoint scr ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint st ∧ (stk s.sp).Disjoint data ∧ (stk s.sp).Disjoint scr ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 768 ≤ 2 ^ 64

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.sp = s₂.sp

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncryptAArch64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0)
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a p, StreamRepr s.mem (s.gpr .x1) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      s.gpr .x2 = BitVec.ofNat 64 a.length → (s.gpr .x3).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
      StreamRepr s'.mem (s.gpr .x1) ciph h iv a c ∧ bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecryptAArch64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0)
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .x1) ciph h iv a c →
      s.gpr .x2 = BitVec.ofNat 64 a.length → (s.gpr .x3).toNat = c.length →
      let c' := c ++ bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
      StreamRepr s'.mem (s.gpr .x1) ciph h iv a c' ∧
        bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_sm4_gcm_stream_finish` needs: `(ctx = x0, state = x1, aad_len = x2,
text_len = x3, tag = x4, work = x5)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x1, 80⟩
  let tag : Region := ⟨s.gpr .x4, 16⟩
  let work : Region := ⟨s.gpr .x5, 768⟩
  3264 ≤ s.sp.toNat ∧ s.rd = [ctx] ∧ s.wr = [st, tag, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧
    tag.Disjoint work ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint st ∧ (stk s.sp).Disjoint tag ∧ (stk s.sp).Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + 768 ≤ 2 ^ 64

/-- `vg_sm4_gcm_stream_finish`. -/
def streamFinishAArch64 : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0)
    let h := ctxH s.mem (s.gpr .x0)
    ∀ iv a c, StreamRepr s.mem (s.gpr .x1) ciph h iv a c →
      s.gpr .x2 = BitVec.ofNat 64 a.length → (s.gpr .x3).toNat = c.length →
      bytesAt s'.mem (s.gpr .x4) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-- What `vg_sm4_gcm_stream_verify` needs: `(ctx = x0, state = x1, aad_len = x2,
text_len = x3, tag = x4, tag_len = x5, work = x6)`. -/
def verPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let st : Region := ⟨s.gpr .x1, 80⟩
  let tag : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let work : Region := ⟨s.gpr .x6, 768⟩
  3264 ≤ s.sp.toNat ∧ s.rd = [ctx, tag] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧ tag.Disjoint work ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint st ∧ (stk s.sp).Disjoint tag ∧ (stk s.sp).Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 768 ≤ 2 ^ 64

/-- `vg_sm4_gcm_stream_verify`. -/
def streamVerifyAArch64 : Contract isa where
  pre := verPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .x0)
    let h := ctxH s.mem (s.gpr .x0)
    let tl := (s.gpr .x5).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .x1) ciph h iv a c →
      s.gpr .x2 = BitVec.ofNat 64 a.length → (s.gpr .x3).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (s.gpr .x4) tl then (s'.gpr .x0).setWidth 32 = 1
      else (s'.gpr .x0).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.sp = s₂.sp

/-- What `vg_sm4_gcm_seal` needs: `(ctx = x0, nonce = x1, nonce_len = x2, aad = x3, aad_len = x4,
data = x5, len = x6, tag = x7, work = [sp])`. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let tag : Region := ⟨s.gpr .x7, 16⟩
  let work : Region := ⟨stackArg s 0, 768⟩
  3264 ≤ s.sp.toNat ∧ s.rd = [ctx, nonce, aad, args s 1] ∧ s.wr = [data, tag, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    nonce.Disjoint work ∧ aad.Disjoint data ∧ aad.Disjoint tag ∧ aad.Disjoint work ∧ data.Disjoint tag ∧
    data.Disjoint work ∧ data.Disjoint (args s 1) ∧ tag.Disjoint work ∧ tag.Disjoint (args s 1) ∧
    work.Disjoint (args s 1) ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint nonce ∧ (stk s.sp).Disjoint aad ∧ (stk s.sp).Disjoint data ∧
    (stk s.sp).Disjoint tag ∧ (stk s.sp).Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x7).toNat + 16 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 768 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 ≤ 2 ^ 64

/-- The public arguments of `seal` and `open`, with `n` on the stack. -/
def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ ∀ i < n, stackArg s₁ i = stackArg s₂ i

/-- `vg_sm4_gcm_seal`. -/
def sealAArch64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .x0)) (ctxH s.mem (s.gpr .x0)) 16
        (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
        (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) =
      (bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat, bytesAt s'.mem (s.gpr .x7) 16)
  pub := onePub 1

/-- What `vg_sm4_gcm_open` needs: `(ctx = x0, nonce = x1, nonce_len = x2, aad = x3, aad_len = x4,
data = x5, len = x6, tag = x7, tag_len = [sp], work = [sp + 8])`. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let tag : Region := ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  let work : Region := ⟨stackArg s 1, 768⟩
  3264 ≤ s.sp.toNat ∧ s.rd = [ctx, nonce, aad, tag, args s 2] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧
    data.Disjoint work ∧ data.Disjoint (args s 2) ∧ tag.Disjoint work ∧ work.Disjoint (args s 2) ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint nonce ∧ (stk s.sp).Disjoint aad ∧ (stk s.sp).Disjoint data ∧
    (stk s.sp).Disjoint tag ∧ (stk s.sp).Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + 768 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 2 ≤ 2 ^ 64

/-- What `vg_sm4_gcm_open` computes, for the arguments of `s`. -/
def openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (s.gpr .x0)) (ctxH s.mem (s.gpr .x0)) (stackArg s 0).toNat
    (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
    (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat)

/-- What `vg_sm4_gcm_open` may leak: whether it succeeds. -/
def openLeakOf (s : State) : List Nat := [if (openRes s).isSome = true then 1 else 0]

/-- `vg_sm4_gcm_open`. -/
def openAArch64 : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat = bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
  pub s₁ s₂ := onePub 2 s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂

end VG.Proof.Sm4Gcm.AArch64
