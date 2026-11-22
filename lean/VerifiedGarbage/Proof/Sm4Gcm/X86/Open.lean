module

import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.Proof.Sm4Gcm.X86.CryptTail
public import VerifiedGarbage.Proof.Gcm.Compose
meta import VerifiedGarbage.Impl.Sm4Gcm.X86
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
meta import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.CryptTail
meta import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.AesGcm.X86.J0
meta import VerifiedGarbage.Proof.AesGcm.X86.J0
public import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
public import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
meta import VerifiedGarbage.Proof.AesGcm.X86.Absorb
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Sm4Gcm.X86.Seal`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.X86.OneTag`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.X86.OneAad`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.X86.OneEntry`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on x86: the entry of `seal` and `open`

Untrusted: everything here is checked by Lean. The precondition of `seal`
and `open` (`OP`), the layout it gives in terms of the public data (`OL`),
what holds of the working space from the entry to the exit (`OEnv`, which
the pieces keep as they write only within `D :: oF p`), and the entry
(`oneEntry_pc`). The state is at `W + 16`. `W` is the last argument, which
the pieces find at 7 in the public data (`pubSw`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)

/-- The state of `seal` and `open`, at `W + 16`. -/
abbrev stOf (W : BitVec 32) : BitVec 32 := W + BitVec.ofNat 32 16

/-- What the precondition of `seal` and `open` (with `nA` arguments, `W` the
last, `w`) gives. -/
structure OP (nA w : Nat) (s : State) : Prop where
  cR : Covers [⟨w64 (arg s 0), 256⟩] (s.rd ++ s.wr)
  nR : Covers [⟨w64 (arg s 1), (arg s 2).toNat⟩] (s.rd ++ s.wr)
  aR : Covers [⟨w64 (arg s 3), (arg s 4).toNat⟩] (s.rd ++ s.wr)
  dW : Covers [⟨w64 (arg s 5), (arg s 6).toNat⟩] s.wr
  wW : Covers [⟨w64 (arg s w), 2560⟩] s.wr
  argR : Covers [⟨argAddr s 0, 4 * nA⟩] (s.rd ++ s.wr)
  c_d : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 5), (arg s 6).toNat⟩
  c_w : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  n_d : (⟨w64 (arg s 1), (arg s 2).toNat⟩ : Region).Disjoint ⟨w64 (arg s 5), (arg s 6).toNat⟩
  n_w : (⟨w64 (arg s 1), (arg s 2).toNat⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  a_d : (⟨w64 (arg s 3), (arg s 4).toNat⟩ : Region).Disjoint ⟨w64 (arg s 5), (arg s 6).toNat⟩
  a_w : (⟨w64 (arg s 3), (arg s 4).toNat⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  d_w : (⟨w64 (arg s 5), (arg s 6).toNat⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  d_a : (⟨w64 (arg s 5), (arg s 6).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 4 * nA⟩
  w_a : (⟨w64 (arg s w), 2560⟩ : Region).Disjoint ⟨argAddr s 0, 4 * nA⟩
  r_d : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 5), (arg s 6).toNat⟩
  r_w : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  k_c : (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s 0), 256⟩
  k_n : (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s 1), (arg s 2).toNat⟩
  k_a : (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s 3), (arg s 4).toNat⟩
  k_d : (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s 5), (arg s 6).toNat⟩
  k_w : (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s w), 2560⟩
  fc : (arg s 0).toNat + 256 ≤ 2 ^ 32
  fn : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  fa : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  fd : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  fw : (arg s w).toNat + 2560 ≤ 2 ^ 32
  sp : 1536 ≤ (s.gpr .esp).toNat
  fg : (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32

theorem op_of_seal {s : State} (h : sealPre s) : OP 9 8 s := by
  simp only [sealPre] at h
  obtain ⟨hrd, hwr, c_d, -, c_w, -, n_d, -, n_w, -, a_d, -, a_w, -, -, d_w, d_a, -, -, w_a, -, -, -, r_d, -, r_w, -,
    k_c, k_n, k_a, k_d, -, k_w, -, fc, fn, fa, fd, -, fw, sp, fg⟩ := h
  rw [ofNat_lit, below_eq sp] at k_c k_n k_a k_d k_w
  exact ⟨by rw [hrd, hwr]; exact covers_of_mem (by simp), by rw [hrd, hwr]; exact covers_of_mem (by simp),
    by rw [hrd, hwr]; exact covers_of_mem (by simp), by rw [hwr]; exact covers_of_mem (by simp),
    by rw [hwr]; exact covers_of_mem (by simp), by rw [hrd, hwr]; exact covers_of_mem (by simp), c_d, c_w, n_d,
    n_w, a_d, a_w, d_w, d_a, w_a, r_d, r_w, k_c, k_n, k_a, k_d, k_w, fc, fn, fa, fd, fw, sp, by omega_arith⟩

/-- The tag `seal` writes. -/
theorem sealPre_tag {s : State} (h : sealPre s) : Covers [⟨w64 (arg s 7), 16⟩] s.wr ∧
    (arg s 7).toNat + 16 ≤ 2 ^ 32 ∧ (⟨w64 (arg s 7), 16⟩ : Region).Disjoint ⟨w64 (arg s 8), 2560⟩ ∧
    (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 7), 16⟩ ∧
    (⟨w64 (arg s 5), (arg s 6).toNat⟩ : Region).Disjoint ⟨w64 (arg s 7), 16⟩ := by
  simp only [sealPre] at h
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, -, -, d_t, -, -, t_w, -, -, -, -, -, -, r_t, -, -, -, -, -, -, -, -, -,
    -, -, -, -, ft, -, -, -⟩ := h
  exact ⟨by rw [hwr]; exact covers_of_mem (by simp), ft, t_w, r_t, d_t⟩

theorem op_of_open {s : State} (h : openPre s) : OP 10 9 s := by
  simp only [openPre] at h
  obtain ⟨hrd, hwr, c_d, c_w, -, n_d, n_w, -, a_d, a_w, -, -, d_w, d_a, -, -, w_a, -, -, -, r_d, -, r_w, -, k_c, k_n,
    k_a, k_d, -, k_w, -, fc, fn, fa, fd, -, fw, sp, fg⟩ := h
  rw [ofNat_lit, below_eq sp] at k_c k_n k_a k_d k_w
  exact ⟨by rw [hrd, hwr]; exact covers_of_mem (by simp), by rw [hrd, hwr]; exact covers_of_mem (by simp),
    by rw [hrd, hwr]; exact covers_of_mem (by simp), by rw [hwr]; exact covers_of_mem (by simp),
    by rw [hwr]; exact covers_of_mem (by simp), by rw [hrd, hwr]; exact covers_of_mem (by simp), c_d, c_w, n_d,
    n_w, a_d, a_w, d_w, d_a, w_a, r_d, r_w, k_c, k_n, k_a, k_d, k_w, fc, fn, fa, fd, fw, sp, by omega_arith⟩

/-- The tag `open` reads. -/
theorem openPre_tag {s : State} (h : openPre s) :
    Covers [⟨w64 (arg s 7), (arg s 8).toNat⟩] (s.rd ++ s.wr) ∧ (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32 ∧
      (⟨w64 (arg s 7), (arg s 8).toNat⟩ : Region).Disjoint ⟨w64 (arg s 9), 2560⟩ ∧
      (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s 7), (arg s 8).toNat⟩ := by
  simp only [openPre] at h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, t_w, -, -, -, -, -, -, -, -, -, -, -, -, -, k_t, -, -, -, -, -,
    -, ft, -, sp, -⟩ := h
  rw [ofNat_lit, below_eq sp] at k_t
  exact ⟨by rw [hrd, hwr]; exact covers_of_mem (by simp), ft, t_w, k_t⟩

theorem stOf_w64 {W : BitVec 32} (hw : W.toNat + 2560 ≤ 2 ^ 32) : w64 (stOf W) = w64 W + BitVec.ofNat 64 16 :=
  w64_add (by omega_arith)

/-- The layout of `seal` and `open`, for the public data `p`. -/
structure OL (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  L : Lay4 (p.2 0) (stOf (p.2 7)) (p.2 7) p.1 1536
  c_d : (⟨w64 (p.2 0), 256⟩ : Region).Disjoint ⟨w64 (p.2 5), (p.2 6).toNat⟩
  n_d : (⟨w64 (p.2 1), (p.2 2).toNat⟩ : Region).Disjoint ⟨w64 (p.2 5), (p.2 6).toNat⟩
  n_w : (⟨w64 (p.2 1), (p.2 2).toNat⟩ : Region).Disjoint ⟨w64 (p.2 7), 2560⟩
  a_d : (⟨w64 (p.2 3), (p.2 4).toNat⟩ : Region).Disjoint ⟨w64 (p.2 5), (p.2 6).toNat⟩
  a_w : (⟨w64 (p.2 3), (p.2 4).toNat⟩ : Region).Disjoint ⟨w64 (p.2 7), 2560⟩
  d_w : (⟨w64 (p.2 5), (p.2 6).toNat⟩ : Region).Disjoint ⟨w64 (p.2 7), 2560⟩
  r_d : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 5), (p.2 6).toNat⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 7), 2560⟩
  k_n : (below p.1 1536).Disjoint ⟨w64 (p.2 1), (p.2 2).toNat⟩
  k_a : (below p.1 1536).Disjoint ⟨w64 (p.2 3), (p.2 4).toNat⟩
  k_d : (below p.1 1536).Disjoint ⟨w64 (p.2 5), (p.2 6).toNat⟩
  fn : (p.2 1).toNat + (p.2 2).toNat ≤ 2 ^ 32
  fa : (p.2 3).toNat + (p.2 4).toNat ≤ 2 ^ 32
  fd : (p.2 5).toNat + (p.2 6).toNat ≤ 2 ^ 32

theorem OP.ol {nA w : Nat} (hw : nA = w + 1) (h8 : 8 ≤ w) {s : State} (h : OP nA w s)
    {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubSw nA 7 s = p) : OL p := by
  obtain a : ∀ i, i < 7 → arg s i = p.2 i := fun i hi => pubSw_arg hp (by omega_arith) (by omega_arith) (by omega_arith)
  obtain aW : arg s w = p.2 7 := pubSw_W hp (by omega_arith) hw
  obtain esp : s.gpr .esp = p.1 := pubSw_esp hp
  obtain ⟨-, -, -, -, -, -, c_d, c_w, n_d, n_w, a_d, a_w, d_w, -, -, r_d, r_w, k_c, k_n, k_a, k_d, k_w, fc, fn, fa,
    fd, fw, sp, -⟩ := h
  obtain e := fun i hi => a i hi
  simp only [e 0 (by omega_arith), e 1 (by omega_arith), e 2 (by omega_arith), e 3 (by omega_arith), e 4 (by omega_arith),
    e 5 (by omega_arith), e 6 (by omega_arith), aW, esp] at c_d c_w n_d n_w a_d a_w d_w r_d r_w k_c k_n
  simp only [e 0 (by omega_arith), e 1 (by omega_arith), e 2 (by omega_arith), e 3 (by omega_arith), e 4 (by omega_arith), e 5 (by omega_arith),
    e 6 (by omega_arith), aW, esp] at k_a k_d k_w fc fn fa fd fw sp
  obtain hs := stOf_w64 fw
  obtain sw : (⟨w64 (stOf (p.2 7)), 80⟩ : Region).Sub ⟨w64 (p.2 7), 2560⟩ := by
    rw [hs]; exact Lay.wSub (by decide)
  refine ⟨Lay4.of fc (by rw [toNat_add32 (by omega_arith)]; omega_arith) fw (by decide) sp
    (c_w.sub_right sw) c_w ?_ ?_ k_c (k_w.sub_right sw) k_w, c_d, n_d, n_w, a_d, a_w, d_w,
    r_d, r_w, k_n, k_a, k_d, fn, fa, fd⟩
  · rw [hs]
    have := Lay.w_w (W := p.2 7) (a := 16) (n := 80) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  · rw [hs]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)

/-- The regions of `W` and the stack the pieces write (but the tag at `W`). -/
abbrev oF (p : BitVec 32 × (Nat → BitVec 32)) : List Region :=
  [⟨w64 (p.2 7) + BitVec.ofNat 64 16, 112⟩, ⟨w64 (p.2 7) + BitVec.ofNat 64 auxO, 4⟩, ⟨w64 (p.2 7) + BitVec.ofNat 64 rO, 16⟩, wsR (p.2 7),
    below p.1 1536]

/-- Those, the data and the first block of `W`: what `OEnv` survives. -/
abbrev oFF (p : BitVec 32 × (Nat → BitVec 32)) : List Region :=
  ⟨w64 (p.2 7), 16⟩ :: ⟨w64 (p.2 5), (p.2 6).toNat⟩ :: oF p

/-- What holds from the entry of `seal` or `open` to the exit. -/
structure OEnv (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  env : Env (p.2 0) (stOf (p.2 7)) (p.2 7) p.1 s
  aadO : slotv s.mem (p.2 7) aadO = p.2 3
  alO : slotv s.mem (p.2 7) alO = p.2 4
  dataO : slotv s.mem (p.2 7) dataO = p.2 5
  lenO : slotv s.mem (p.2 7) lenO = p.2 6
  zO : slotv s.mem (p.2 7) zO = 0
  nlO : slotv s.mem (p.2 7) nlO = p.2 2
  tp : slotv s.mem (p.2 7) tpO = arg s₀ 7
  saved : SavedAt s.mem (p.2 7) s₀
  ret : s.mem.readW (w64 p.1) 32 = s₀.mem.readW (w64 p.1) 32
  ciph : ciphOf s.mem (p.2 0) = ctxCiph s₀.mem (w64 (p.2 0))
  hk : Hk s.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0))
  aad : bytesAt s.mem (w64 (p.2 3)) (p.2 4).toNat = bytesAt s₀.mem (w64 (p.2 3)) (p.2 4).toNat
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  nIn : Covers [⟨w64 (p.2 1), (p.2 2).toNat⟩] (s.rd ++ s.wr)
  aIn : Covers [⟨w64 (p.2 3), (p.2 4).toNat⟩] (s.rd ++ s.wr)
  dIn : Covers [⟨w64 (p.2 5), (p.2 6).toNat⟩] s.wr

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

/-- A part of the kept values, outside what the pieces write. -/
theorem slot_oF {o n : Nat} (h₁ : 128 ≤ o)
    (h₂ : o + n ≤ auxO ∨ (auxO + 4 ≤ o ∧ o + n ≤ rO) ∨ (rO + 16 ≤ o ∧ o + n ≤ 240)) :
    ∀ r ∈ oFF p, (⟨w64 (p.2 7) + BitVec.ofNat 64 o, n⟩ : Region).Disjoint r := by
  simp only [auxO, rO] at h₂
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := Lay.w_w (W := p.2 7) (a := o) (n := n) (d := 0) (k := 16) (.inr (by omega_arith)) (by omega_arith) (by decide)
    rwa [BitVec.add_zero] at this
  · exact (G.d_w.sub_right (Lay.wSub (by omega_arith))).symm
  · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact Lay.w_w (by simp only [auxO]; omega_arith) (by omega_arith) (by decide)
  · exact Lay.w_w (by simp only [rO]; omega_arith) (by omega_arith) (by decide)
  · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (G.L.stk_w (by omega_arith)).symm

/-- The context, outside what the pieces write. -/
theorem ctx_oF : ∀ r ∈ oFF p, (⟨w64 (p.2 0), 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact G.L.cw.sub_right (Region.sub_prefix (by decide))
  · exact G.c_d
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.kc.symm

/-- The additional data, outside what the pieces write. -/
theorem aad_oF : ∀ r ∈ oFF p, (⟨w64 (p.2 3), (p.2 4).toNat⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact G.a_w.sub_right (Region.sub_prefix (by decide))
  · exact G.a_d
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.k_a.symm

/-- The return address, outside what the pieces write. -/
theorem ret_oF : ∀ r ∈ oFF p, (⟨w64 p.1, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact G.r_w.sub_right (Region.sub_prefix (by decide))
  · exact G.r_d
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact ret_below G.L.sp

/-- `OEnv` after code that writes within `oFF p` and keeps the registers. -/
theorem OEnv.frame {s₀ s s' : State} (h : OEnv p s₀ s)
    (hf : Frame (oFF p) s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : OEnv p s₀ s' := by
  obtain sl : ∀ o, 128 ≤ o → (o + 4 ≤ auxO ∨ (auxO + 4 ≤ o ∧ o + 4 ≤ rO) ∨ (rO + 16 ≤ o ∧ o + 4 ≤ 240)) →
      slotv s'.mem (p.2 7) o = slotv s.mem (p.2 7) o := fun o h₁ h₂ => by
    rw [slotv_eq, slotv_eq]; exact slot_frame hf (slot_oF G h₁ h₂)
  refine ⟨h.env.keep hbp hsi hsp hrd hwr ?_,
    by rw [sl _ (by decide) (by decide)]; exact h.aadO, by rw [sl _ (by decide) (by decide)]; exact h.alO,
    by rw [sl _ (by decide) (by decide)]; exact h.dataO, by rw [sl _ (by decide) (by decide)]; exact h.lenO,
    by rw [sl _ (by decide) (by decide)]; exact h.zO, by rw [sl _ (by decide) (by decide)]; exact h.nlO,
    by rw [sl _ (by decide) (by decide)]; exact h.tp, h.saved.frame hf fun r hr => ?_, by rw [ret_kept hf (ret_oF G)]; exact h.ret,
    by rw [ciph_frame hf (ctx_oF G)]; exact h.ciph,
    by rw [show Hk s'.mem (p.2 0) = Hk s.mem (p.2 0) from blockAt_frame hf fun r hr =>
      (ctx_oF G r hr).sub_left (Lay.ctxSub (by decide))]; exact h.hk,
    by rw [bytesAt_frame hf (aad_oF G) (by omega_arith)]; exact h.aad, by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr,
    by rw [hrd, hwr]; exact h.nIn, by rw [hrd, hwr]; exact h.aIn, by rw [hwr]; exact h.dIn⟩
  · have := sl ctxO (by decide) (by decide); rwa [slotv_eq, slotv_eq] at this
  · exact slot_oF G (o := 128) (n := 16) (by decide) (by decide) r hr

theorem OEnv.frameE {s₀ s s' : State} (h : OEnv p s₀ s)
    (hf : Frame (oFF p) s.mem s'.mem)
    (he : Env (p.2 0) (stOf (p.2 7)) (p.2 7) p.1 s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : OEnv p s₀ s' :=
  h.frame G hf (by rw [he.ebp, h.env.ebp]) (by rw [he.esi, h.env.esi]) (by rw [he.esp, h.env.esp]) hrd hwr

/-- A part of the state, in `W`. -/
theorem st_eq {d : Nat} : w64 (stOf (p.2 7)) + BitVec.ofNat 64 d = w64 (p.2 7) + BitVec.ofNat 64 (16 + d) := by
  rw [stOf_w64 G.L.fw, Offset.add_add]

omit G in
/-- A part of `W` the pieces write. -/
theorem w_sub_oF {d k : Nat} (h₁ : 16 ≤ d) (h₂ : d + k ≤ 128) :
    ∃ r' ∈ oF p, Region.Sub ⟨w64 (p.2 7) + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨w64 (p.2 7) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩

theorem st_sub_oF {d k : Nat} (h : d + k ≤ 80) :
    ∃ r' ∈ oF p, Region.Sub ⟨w64 (stOf (p.2 7)) + BitVec.ofNat 64 d, k⟩ r' := by
  rw [st_eq G]; exact w_sub_oF (by omega_arith) (by omega_arith)

theorem st0_sub_oF {k : Nat} (h : k ≤ 80) : ∃ r' ∈ oF p, Region.Sub ⟨w64 (stOf (p.2 7)), k⟩ r' := by
  rw [stOf_w64 G.L.fw]; exact w_sub_oF (by omega_arith) (by omega_arith)

omit G in
theorem ws_sub_oF : ∃ r' ∈ oF p, Region.Sub (wsR (p.2 7)) r' :=
  ⟨_, by simp, fun _ h => h⟩

omit G in
theorem stk_sub_oF : ∃ r' ∈ oF p, Region.Sub (below p.1 1536) r' :=
  ⟨_, by simp, fun _ h => h⟩

/-- The stack AES-GCM's pieces use. -/
theorem stk28_sub_oF : ∃ r' ∈ oF p, Region.Sub (below p.1 28) r' :=
  ⟨_, by simp, G.L.below28⟩

omit G in
theorem pslot_sub_oF : ∃ r' ∈ oF p, Region.Sub (pslotR (p.2 7)) r' :=
  ⟨_, by simp, pslot_ws _⟩

omit G in
theorem Frame.oD {m m' : Mem} (h : Frame (oF p) m m') : Frame (oFF p) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)

omit G in
theorem Frame.oDD {m m' : Mem} (h : Frame (⟨w64 (p.2 5), (p.2 6).toNat⟩ :: oF p) m m') : Frame (oFF p) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

omit G in
theorem d_sub_oF :
    ∃ r' ∈ ⟨w64 (p.2 5), (p.2 6).toNat⟩ :: oF p, Region.Sub ⟨w64 (p.2 5), (p.2 6).toNat⟩ r' :=
  ⟨_, by simp, fun _ h => h⟩

end

/-! ## The entry -/

abbrev oKeeps : List (Nat × Nat) :=
  [(0, ctxO), (1, dO), (2, nO), (2, nlO), (3, aadO), (4, alO), (5, dataO), (6, lenO)]

abbrev oPre : List Instr := [.mov .esi (.reg .ebp), .alu .add .esi (imm stO)]

abbrev oTail : List Instr := [.mov .eax (imm 0), .store (at_ .ebp zO) .eax]

theorem oneEntry_eq (w : Nat) (ex : List (Nat × Nat)) :
    oneEntry w (ex.flatMap (fun (p : Nat × Nat) => keep p.1 p.2)) =
      entry w (oPre ++ ((oKeeps ++ ex).flatMap (fun (p : Nat × Nat) => keep p.1 p.2) ++ oTail)) := by
  simp only [oneEntry, oKeeps, oPre, oTail, List.cons_append, List.flatMap_cons, List.append_assoc, List.nil_append]

/-- The end of the entry: `zO` zeroed. -/
theorem oTail_ok {W : BitVec 32} {s : State} (hbp : s.gpr .ebp = W) (hw : Covers [⟨w64 W, 2560⟩] s.wr)
    (fw : W.toNat + 2560 ≤ 2 ^ 32) :
    ∃ s', runBlock isa oTail s = some s' ∧ Frame [⟨w64 W + BitVec.ofNat 64 zO, 4⟩] s.mem s'.mem ∧
      slotv s'.mem W zO = 0 ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => w64_add (by omega_arith)
  obtain wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => in_off hw ho (by decide)
  obtain f₁ : Frame [⟨w64 W + BitVec.ofNat 64 zO, 4⟩] s.mem
      (s.mem.writeW (w64 W + BitVec.ofNat 64 zO) (BitVec.ofNat 32 0)) :=
    (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)
  exact ⟨_, by xrun [hbp, aW, wIn], by mems []; exact f₁, by mems [slotv_eq]; rfl, by regs [], by regs [], by regs [],
    by mems [], by mems []⟩

/-- After the entry of `seal` or `open`: the nonce ready for `j0`, and the
inputs as they were. -/
structure OEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  o : OEnv p s₀ s
  dO : slotv s.mem (p.2 7) dO = p.2 1
  nO : slotv s.mem (p.2 7) nO = p.2 2
  iv : bytesAt s.mem (w64 (p.2 1)) (p.2 2).toNat = bytesAt s₀.mem (w64 (p.2 1)) (p.2 2).toNat
  data : bytesAt s.mem (w64 (p.2 5)) (p.2 6).toNat = bytesAt s₀.mem (w64 (p.2 5)) (p.2 6).toNat
  frame : Frame [⟨w64 (p.2 7) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem

/-- The entry of `seal` and `open` (with `nA` arguments, `W` the last, `w`),
copying also the arguments `ex`, `tag` (the argument 8) among them. -/
theorem oneEntry_pc (nA w : Nat) (hw : nA = w + 1) (h8 : 8 ≤ w) (ex : List (Nat × Nat))
    (hex : ∀ q ∈ ex, q.1 < nA ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0 ∧ (q.2 + 4 ≤ zO ∨ zO + 4 ≤ q.2))
    (hnd : ((oKeeps ++ ex).map (·.2)).Nodup) (htp : (7, tpO) ∈ ex) (Pre : State → Prop)
    (hPre : ∀ s, Pre s → OP nA w s) (p : BitVec 32 × (Nat → BitVec 32)) (G : OL p)
    {hh₀ hh : Taint.Hint VG.X86.taint.T}
    (ht₀ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .eax (argOp w)]) hh₀).isSome = true)
    (ht : (VG.X86.taint.check (τr [.eax, .esp]) (.block (saveAt ++ (oPre ++
      ((oKeeps ++ ex).flatMap (fun p => keep p.1 p.2) ++ oTail)))) hh).isSome = true) :
    Pc (fun (s₀ : State) s => Pre s₀ ∧ pubSw nA 7 s₀ = p ∧ s = s₀)
      (oneEntry w (ex.flatMap (fun (p : Nat × Nat) => keep p.1 p.2)))
      (fun s₀ s => OEnt p s₀ s ∧ (∀ q ∈ ex, slotv s.mem (p.2 7) q.2 = arg s₀ q.1) ∧ pubSw nA 7 s₀ = p ∧
        Pre s₀) := by
  rw [oneEntry_eq]
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    obtain h := hPre _ hpre
    obtain a : ∀ i, i < 7 → arg s₀ i = p.2 i := fun i hi => pubSw_arg hpub (by omega_arith) (by omega_arith) (by omega_arith)
    obtain aW : arg s₀ w = p.2 7 := pubSw_W hpub (by omega_arith) hw
    obtain esp := pubSw_esp hpub
    have fw := h.fw
    rw [aW] at fw
    obtain wW : Covers [⟨w64 (p.2 7), 2560⟩] s₀.wr := by rw [← aW]; exact h.wW
    obtain rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by rw [argsR_eq]; exact h.argR
    obtain aw : (argsR (s₀.gpr .esp) nA).Disjoint ⟨w64 (p.2 7), 2560⟩ := by
      rw [argsR_eq, ← aW]; exact h.w_a.symm
    obtain hok : ∀ q ∈ oKeeps, q.1 < 7 ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0 ∧
        (q.2 + 4 ≤ zO ∨ zO + 4 ≤ q.2) := by decide
    obtain hps : ∀ q ∈ oKeeps ++ ex, q.1 < nA ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0 := fun q hq => by
      rcases List.mem_append.mp hq with hq | hq
      · have := hok q hq; exact ⟨by omega_arith, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := hex q hq; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
    refine entry_gen (St := stOf (p.2 7)) _ (oKeeps ++ ex) _ (by omega_arith) hps hnd aW wW rA aw h.fg fw
      (fun s₁ bp sp rd wr _ => ⟨_, by xrun [bp], by regs [bp], fun r hr => by
        simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ hr], by mems [], by mems [], by mems []⟩) fun s₂ e => ?_
    obtain ⟨s₃, run, f₃, z₃, bp₃, si₃, sp₃, rd₃, wr₃⟩ := oTail_ok (W := p.2 7) e.ebp (by rw [e.wr]; exact wW) fw
    have L := G.L
    -- What the tail writes.
    obtain st : ∀ o, 128 ≤ o → o + 4 ≤ 2560 → (o + 4 ≤ zO ∨ zO + 4 ≤ o) →
        slotv s₃.mem (p.2 7) o = slotv s₂.mem (p.2 7) o := fun o h₁ h₂ h₃ => by
      rw [slotv_eq, slotv_eq]
      refine slot_frame f₃ fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [zO] at h₃
      exact Lay.w_w (by simp only [zO]; omega_arith) (by omega_arith) (by decide)
    obtain f₃' : Frame [⟨w64 (p.2 7) + BitVec.ofNat 64 128, 2432⟩] s₂.mem s₃.mem := f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    obtain fE : Frame [⟨w64 (p.2 7) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s₃.mem := e.frame.trans f₃'
    obtain dE : ∀ {q : Addr} {n : Nat}, (⟨q, n⟩ : Region).Disjoint ⟨w64 (p.2 7), 2560⟩ →
        ∀ r ∈ [(⟨w64 (p.2 7) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨q, n⟩ : Region).Disjoint r :=
      fun hq r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hq.sub_right (Lay.wSub (by decide))
    obtain slR : ∀ q ∈ oKeeps ++ ex, slotv s₃.mem (p.2 7) q.2 = arg s₀ q.1 := fun q hq => by
      obtain hz : q.2 + 4 ≤ zO ∨ zO + 4 ≤ q.2 := by
        rcases List.mem_append.mp hq with hq | hq
        · exact (hok q hq).2.2.2.2
        · exact (hex q hq).2.2.2.2
      rw [st _ (by have := (hps q hq).2.1; omega_arith) (hps q hq).2.2.1 hz, e.slots q hq]
    obtain sl : ∀ q ∈ oKeeps, slotv s₃.mem (p.2 7) q.2 = p.2 q.1 := fun q hq => by
      rw [slR q (List.mem_append_left _ hq), a _ (hok q hq).1]
    obtain he : Env (p.2 0) (stOf (p.2 7)) (p.2 7) p.1 s₃ := by
      refine ⟨by rw [bp₃, e.ebp], by rw [si₃, e.esi], by rw [sp₃, e.esp, esp], ?_, ?_, by rw [wr₃, e.wr]; exact wW,
        by have := sl (0, ctxO) (by simp); rwa [slotv_eq] at this⟩
      · rw [rd₃, wr₃, e.rd, e.wr, ← a 0 (by omega_arith)]; exact h.cR
      · rw [wr₃, e.wr, stOf_w64 fw]; exact covers_off wW (by decide) (by decide)
    refine ⟨s₃, run, ⟨⟨he, sl (3, aadO) (by simp),
      sl (4, alO) (by simp), sl (5, dataO) (by simp), sl (6, lenO) (by simp), z₃, sl (2, nlO) (by simp),
      slR (7, tpO) (List.mem_append_right _ htp), ?_, ?_, ?_, ?_, ?_, by rw [rd₃, e.rd], by rw [wr₃, e.wr], ?_, ?_, ?_⟩,
      sl (1, dO) (by simp), sl (2, nO) (by simp), ?_, ?_, fE⟩, fun q hq => slR q (List.mem_append_right _ hq), hpub,
      hpre⟩
    · exact e.saved.frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [← esp, ret_kept fE (dE (by rw [esp]; exact G.r_w))]
    · exact ciph_frame fE (dE G.L.cw)
    · rw [ctxH_eq]; exact blockAt_frame fE (dE (G.L.cw.sub_left (Lay.ctxSub (by decide))))
    · exact bytesAt_frame fE (dE G.a_w) (by omega_arith)
    · rw [rd₃, wr₃, e.rd, e.wr, ← a 1 (by omega_arith), ← a 2 (by omega_arith)]; exact h.nR
    · rw [rd₃, wr₃, e.rd, e.wr, ← a 3 (by omega_arith), ← a 4 (by omega_arith)]; exact h.aR
    · rw [wr₃, e.wr, ← a 5 (by omega_arith), ← a 6 (by omega_arith)]; exact h.dW
    · exact bytesAt_frame fE (dE G.n_w) (by omega_arith)
    · exact bytesAt_frame fE (dE G.d_w) (by omega_arith)
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 7 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubSw_esp h₁, pubSw_esp h₂]) ht₀) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) ht)
    subst s
    obtain h := hPre _ hpre
    obtain rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by rw [argsR_eq]; exact h.argR
    exact WP.mono (arg0_ok (argIn_of rA h.fg (by omega_arith))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubSw_W hpub (by omega_arith) hw, by rw [sp]; exact pubSw_esp hpub⟩

end VG.Proof.Sm4Gcm.X86

end

end

/-!
# SM4-GCM on x86: `J₀` and the additional data of `seal` and `open`

Untrusted: everything here is checked by Lean. `oneAad` (`oneAad_pc`):
`J₀` and the first counter block (`j0`), then the additional data absorbed
(`absorb 16`) and padded (`flush 16`), all within `oF p`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl} {ci : CtrImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen inc32)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed)

/-- After `oneAad`: `J₀`, the additional data absorbed and padded, and the
first counter block. -/
structure OAad (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  o : OEnv p s₀ s
  j : blockAt s.mem (w64 (stOf (p.2 7))) =
    Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 1)) (p.2 2).toNat)
  y : Absorbed s.mem (w64 (stOf (p.2 7)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 7)) + BitVec.ofNat 64 32)
    (ctxH s₀.mem (w64 (p.2 0)))
    (bytesAt s₀.mem (w64 (p.2 3)) (p.2 4).toNat ++ zeros (padLen (p.2 4).toNat))
  cb : blockAt s.mem (w64 (stOf (p.2 7)) + BitVec.ofNat 64 48) =
    inc32 (Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 1)) (p.2 2).toNat))

/-- What holds between the pieces of `oneAad`: `J₀` and the first counter
block written, within `oF p` since `sE`. -/
structure OJ (p : BitVec 32 × (Nat → BitVec 32)) (sE s₀ s : State) : Prop where
  ent : OEnt p s₀ sE
  o : OEnv p s₀ s
  fr : Frame (oF p) sE.mem s.mem
  j : blockAt s.mem (w64 (stOf (p.2 7))) =
    Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 1)) (p.2 2).toNat)
  cb : blockAt s.mem (w64 (stOf (p.2 7)) + BitVec.ofNat 64 48) =
    inc32 (Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 1)) (p.2 2).toNat))

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

/-- The arguments of a piece from two kept slots: `dO := [so]`, `nO := [sl]`, `bO := 0`. -/
theorem setP_ok {so sl : Nat} (h₁ : 128 ≤ so) (h₂ : so + 4 ≤ 240) (h₃ : 128 ≤ sl) (h₄ : sl + 4 ≤ 240)
    {s : State} (he : Env (p.2 0) (stOf (p.2 7)) (p.2 7) p.1 s) :
    ∃ s', runBlock isa [.mov .eax (slot so), .store (at_ .ebp dO) .eax, .mov .eax (slot sl),
        .store (at_ .ebp nO) .eax, .mov .eax (imm 0), .store (at_ .ebp bO) .eax] s = some s' ∧
      slotv s'.mem (p.2 7) dO = slotv s.mem (p.2 7) so ∧ slotv s'.mem (p.2 7) nO = slotv s.mem (p.2 7) sl ∧
      slotv s'.mem (p.2 7) bO = 0 ∧ Frame [pslotR (p.2 7)] s.mem s'.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have L := G.L
  have ho : so < 2560 := by omega
  have hl : sl < 2560 := by omega
  have r₁ := he.wIn' (d := so) (n := 4) (by omega)
  have r₂ := he.wIn' (d := sl) (n := 4) (by omega)
  have e₁ : (s.mem.writeW (w64 (p.2 7) + BitVec.ofNat 64 dO) (s.mem.readW (w64 (p.2 7) + BitVec.ofNat 64 so) 32)).readW
      (w64 (p.2 7) + BitVec.ofNat 64 sl) 32 = s.mem.readW (w64 (p.2 7) + BitVec.ofNat 64 sl) 32 :=
    readW_writeW_off _ _ _ (by simp only [dO]; omega) (by omega) (by decide)
  refine ⟨_, by xrun [he.ebp, L.aW ho, L.aW hl, L.aW, he.wIn, r₁, r₂, e₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [slotv_eq]
  · mems [slotv_eq]
  · mems [slotv_eq]; rfl
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    exact pslot_write (pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide)
      (by decide) _) (by decide) (by decide) _
  · regs []
  · regs []
  · regs []
  · mems []
  · mems []

/-- `bO := [sl] mod 16`. -/
theorem setB_ok {sl : Nat} (h₃ : 128 ≤ sl) (h₄ : sl + 4 ≤ 240) {s : State}
    (he : Env (p.2 0) (stOf (p.2 7)) (p.2 7) p.1 s) :
    ∃ s', runBlock isa [.mov .eax (slot sl), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax] s = some s' ∧
      slotv s'.mem (p.2 7) bO = BitVec.ofNat 32 ((slotv s.mem (p.2 7) sl).toNat % 16) ∧
      Frame [pslotR (p.2 7)] s.mem s'.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have L := G.L
  have hl : sl < 2560 := by omega
  have r₂ := he.wIn' (d := sl) (n := 4) (by omega_using [h₄])
  have hand := and15 (s.mem.readW (w64 (p.2 7) + BitVec.ofNat 64 sl) 32)
  refine ⟨_, by xrun [he.ebp, L.aW hl, L.aW, he.wIn, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [slotv_eq]; rw [hand]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    exact pslot_write (Frame.refl _ _) (by decide) (by decide) _
  · regs []
  · regs []
  · regs []
  · mems []
  · mems []

theorem j0Frame_oF : ∀ r ∈ j0Frame (stOf (p.2 7)) (p.2 7) p.1 28, ∃ r' ∈ oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st0_sub_oF G (by decide)
  · exact w_sub_oF (by decide) (by decide)
  · exact ws_sub_oF
  · exact stk28_sub_oF G

theorem absFrame_oF : ∀ r ∈ absFrame (stOf (p.2 7)) (p.2 7) p.1 28 16, ∃ r' ∈ oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st_sub_oF G (by decide)
  · exact st_sub_oF G (by decide)
  · exact ws_sub_oF
  · exact stk28_sub_oF G

theorem tFrame_oF : ∀ r ∈ tFrame (stOf (p.2 7)) (p.2 7) p.1 28 16, ∃ r' ∈ oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st_sub_oF G (by decide)
  · exact w_sub_oF (by decide) (by decide)
  · exact ws_sub_oF
  · exact stk28_sub_oF G

/-- A block of the state that `absorb 16` and `flush 16` keep (`J₀`, the counter block). -/
theorem st_absFrame {d : Nat} (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 80)) :
    ∀ r ∈ absFrame (stOf (p.2 7)) (p.2 7) p.1 28 16,
      (⟨w64 (stOf (p.2 7)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega_using [hd]) (by omega_using [hd]) (by decide)
  · exact Lay.st_st (by omega_using [hd]) (by omega_using [hd]) (by decide)
  · exact G.L.st_w (by omega_using [hd]) (.inr ⟨by decide, by decide⟩)
  · exact (G.L.lay.stk_st (by omega_using [hd])).symm

theorem st_tFrame {d : Nat} (hd : d + 16 ≤ 16 ∨ (32 ≤ d ∧ d + 16 ≤ 80)) :
    ∀ r ∈ tFrame (stOf (p.2 7)) (p.2 7) p.1 28 16,
      (⟨w64 (stOf (p.2 7)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega_using [hd]) (by omega_using [hd]) (by decide)
  · exact G.L.st_w (by omega_using [hd]) (.inr ⟨by decide, by decide⟩)
  · exact G.L.st_w (by omega_using [hd]) (.inr ⟨by decide, by decide⟩)
  · exact (G.L.lay.stk_st (by omega_using [hd])).symm

theorem st_pslot {d : Nat} (hd : d + 16 ≤ 80) :
    ∀ r ∈ [pslotR (p.2 7)], (⟨w64 (stOf (p.2 7)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact G.L.st_w (by omega_using [hd]) (.inr ⟨by decide, by decide⟩)

theorem oneAad_pc :
    Pc (fun (b : State × State) s => OEnt p b.1 s ∧ s = b.2) (oneAad vg.callees)
      (fun b s' => OAad p b.1 s' ∧ Frame (oF p) b.2.mem s'.mem) := by
  have L := G.L
  have sW : (⟨w64 (stOf (p.2 7)), 80⟩ : Region).Sub ⟨w64 (p.2 7), 2560⟩ := by
    rw [stOf_w64 L.fw]; exact Lay.wSub (by decide)
  -- `J₀`.
  refine Pc.seq (Q := fun b s => OJ p b.2 b.1 s ∧
      blockAt s.mem (w64 (stOf (p.2 7)) + BitVec.ofNat 64 16) = 0)
    (Pc.mono (Pc.lift (j0_pc L.lay (D := p.2 1) (n := (p.2 2).toNat)) (fun _ s => s.mem) fun b s ⟨h, _⟩ =>
      ⟨⟨h.o.env, h.dO, by rw [h.nO, ofNat_toNat32], by rw [h.o.nlO, ofNat_toNat32], h.o.zO, (p.2 2).isLt,
        ⟨h.o.nIn, G.fn, G.n_w.sub_right sW, G.n_w, G.k_n.sub_left G.L.below28⟩⟩, rfl⟩) (fun _ _ h => h)
      fun b s ⟨sE, ⟨h, hs⟩, ho, rd, wr⟩ => by
        subst hs
        exact ⟨⟨h, h.o.frameE G (Frame.oD (ho.frame.sub (j0Frame_oF G))) ho.env rd wr,
          ho.frame.sub (j0Frame_oF G), by rw [ho.j0, h.o.hk, h.iv], by rw [ho.cb, h.o.hk, h.iv]⟩, ho.y⟩) ?_
  -- The additional data's arguments.
  refine Pc.seq (Q := fun b s => OJ p b.2 b.1 s ∧
      blockAt s.mem (w64 (stOf (p.2 7)) + BitVec.ofNat 64 16) = 0 ∧
      AbsIn (p.2 0) (stOf (p.2 7)) (p.2 7) p.1 28 (p.2 3) (p.2 4).toNat 0 s)
    (Pc.taint [.ebp] (fun b s ⟨h, y0⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s', run, d, n, bz, f, bp, si, sp, rd, wr⟩ := setP_ok G (so := aadO) (sl := alO) (by decide) (by decide)
      (by decide) (by decide) h.o.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have fo : Frame (oF p) s.mem s'.mem := f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact pslot_sub_oF
    have o' := h.o.frame G (Frame.oD fo) bp si sp rd wr
    refine ⟨⟨h.ent, o', h.fr.trans fo, by
        have e := blockAt_frame f (st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact h.j,
        by rw [blockAt_frame f (st_pslot G (by decide))]; exact h.cb⟩,
      by rw [blockAt_frame f (st_pslot G (by decide))]; exact y0, ⟨o'.env, by rw [d]; exact h.o.aadO,
        by rw [n, h.o.alO, ofNat_toNat32], by rw [bz]; rfl, by decide, (p.2 4).isLt,
        ⟨o'.aIn, G.fa, G.a_w.sub_right sW, G.a_w, G.k_a.sub_left G.L.below28⟩⟩⟩
  -- Absorbed.
  refine Pc.seq (Q := fun b s => OJ p b.2 b.1 s ∧
      Absorbed s.mem (w64 (stOf (p.2 7)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 7)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (bytesAt b.1.mem (w64 (p.2 3)) (p.2 4).toNat))
    (Pc.mono (Pc.lift (absorb_pc L.lay (yo := 16) (.inr rfl) (b := 0) (by decide) (p.2 4).isLt) (fun _ s => s.mem)
      fun b s ⟨_, _, ha⟩ => ⟨ha, rfl⟩) (fun _ _ h => h)
      fun b s' ⟨s, ⟨h, y0, _⟩, ho, rd, wr⟩ => ⟨⟨h.ent, h.o.frameE G
        (Frame.oD (ho.frame.sub (absFrame_oF G))) ho.env rd wr, h.fr.trans (ho.frame.sub (absFrame_oF G)), ?_, ?_⟩,
        ?_⟩) ?_
  · have := blockAt_frame ho.frame (st_absFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact h.j
  · rw [blockAt_frame ho.frame (st_absFrame G (.inr ⟨by decide, by decide⟩))]; exact h.cb
  · have := ho.abs [] rfl (Proof.Gcm.absorbed_nil _ y0)
    rwa [List.nil_append, h.o.hk, h.o.aad] at this
  -- `bO`.
  refine Pc.seq (Q := fun b s => OJ p b.2 b.1 s ∧
      Absorbed s.mem (w64 (stOf (p.2 7)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 7)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (bytesAt b.1.mem (w64 (p.2 3)) (p.2 4).toNat) ∧
      slotv s.mem (p.2 7) bO = BitVec.ofNat 32 ((p.2 4).toNat % 16))
    (Pc.taint [.ebp] (fun b s ⟨h, ha⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s', run, bz, f, bp, si, sp, rd, wr⟩ := setB_ok G (sl := alO) (by decide) (by decide) h.o.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have fo : Frame (oF p) s.mem s'.mem := f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact pslot_sub_oF
    have o' := h.o.frame G (Frame.oD fo) bp si sp rd wr
    have hl := length_bytesAt b.1.mem (w64 (p.2 3)) (p.2 4).toNat
    refine ⟨⟨h.ent, o', h.fr.trans fo, by
        have e := blockAt_frame f (st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact h.j,
        by rw [blockAt_frame f (st_pslot G (by decide))]; exact h.cb⟩,
      ha.congr (blockAt_frame f (st_pslot G (by decide))) (bytesAt_frame f (fun r hr =>
        (st_pslot G (d := 32) (by decide) r hr).sub_left (Region.sub_prefix (by omega_using []))) (by omega_using [])),
      by rw [bz, h.o.alO]⟩
  -- Padded.
  refine Pc.mono (Pc.lift (flush_pc L.lay (yo := 16) (.inr rfl) (b := (p.2 4).toNat % 16) (Nat.mod_lt _ (by decide)))
    (fun _ s => s.mem) fun b s ⟨h, _, hb⟩ => ⟨⟨h.o.env, hb⟩, rfl⟩) (fun _ _ h => h)
    fun b s' ⟨s, ⟨h, ha, _⟩, ho, rd, wr⟩ => ⟨⟨h.o.frameE G
      (Frame.oD (ho.frame.sub (tFrame_oF G))) ho.env rd wr, ?_, ?_, ?_⟩, h.fr.trans (ho.frame.sub (tFrame_oF G))⟩
  · have := blockAt_frame ho.frame (st_tFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact h.j
  · have hl := length_bytesAt b.1.mem (w64 (p.2 3)) (p.2 4).toNat
    have := ho.abs _ (by rw [hl]) (by rw [h.o.hk]; exact ha)
    rwa [h.o.hk, hl] at this
  · rw [blockAt_frame ho.frame (st_tFrame G (.inr ⟨by decide, by decide⟩))]; exact h.cb

end

end VG.Proof.Sm4Gcm.X86

end

end

/-!
# SM4-GCM on x86: the data and the tag of `seal` and `open`

Untrusted: everything here is checked by Lean. `oneCrypt` (`oneCrypt_pc`):
the data XORed with the keystream from a counter block; and `oneTag o`
(`oneTag_pc`): the data absorbed and padded, then the tag into `W + o`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl} {ci : CtrImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen inc32 ghash ghashFrom blocks toBytes ofBytes)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

theorem oneCrypt_eq : (oneCrypt ci.fn) = .seq (.block [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax,
    .mov .eax (slot lenO), .store (at_ .ebp nO) .eax, .mov .eax (imm 0), .store (at_ .ebp bO) .eax]) (crypt ci.fn) := rfl

theorem oneTag_eq (o : Nat) : (oneTag vg.callees ci.fn) o = .seq (.block [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax,
    .mov .eax (slot lenO), .store (at_ .ebp nO) .eax, .mov .eax (imm 0), .store (at_ .ebp bO) .eax])
  (.seq (absorb vg.callees 16)
  (.seq (.block [.mov .eax (slot lenO), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax])
  (.seq (flush vg.callees 16) (tag vg.callees ci.fn o alO zO lenO zO)))) := rfl

/-- What GHASH has absorbed before the data: the additional data, padded. -/
abbrev xA (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : List Byte :=
  bytesAt s₀.mem (w64 (p.2 3)) (p.2 4).toNat ++ zeros (padLen (p.2 4).toNat)

/-- `J₀`. -/
abbrev jOf (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : Block :=
  Spec.Gcm.j0 (ctxH s₀.mem (w64 (p.2 0))) (bytesAt s₀.mem (w64 (p.2 1)) (p.2 2).toNat)

/-- Before `oneTag o`. -/
structure OTIn (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  o : OEnv p s₀ s
  j : blockAt s.mem (w64 (stOf (p.2 7))) = jOf p s₀
  y : Absorbed s.mem (w64 (stOf (p.2 7)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 7)) + BitVec.ofNat 64 32)
    (ctxH s₀.mem (w64 (p.2 0))) (xA p s₀)

/-- The regions `oneTag o` writes: the state's first three blocks, `T`, the
tag at `W + o`, the working space and the stack. -/
abbrev oT (p : BitVec 32 × (Nat → BitVec 32)) (o : Nat) : List Region :=
  [⟨w64 (p.2 7) + BitVec.ofNat 64 16, 48⟩, ⟨w64 (p.2 7) + BitVec.ofNat 64 96, 16⟩,
    ⟨w64 (p.2 7) + BitVec.ofNat 64 o, 16⟩, wsR (p.2 7), below p.1 1536]

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

omit G in
theorem pslot_oF {m m' : Mem} (f : Frame [pslotR (p.2 7)] m m') : Frame (oF p) m m' :=
  f.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pslot_sub_oF

theorem crFrame_oF : ∀ r ∈ crFrame (stOf (p.2 7)) (p.2 7) p.1 1536 (p.2 5) (p.2 6).toNat,
    ∃ r' ∈ ⟨w64 (p.2 5), (p.2 6).toNat⟩ :: oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact d_sub_oF
  · obtain ⟨r', h₁, h₂⟩ := st_sub_oF G (d := 48) (k := 32) (by decide)
    exact ⟨r', List.mem_cons_of_mem _ h₁, h₂⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The data, writable, for `crypt`. -/
theorem dataW_of {s₀ s : State} (h : OEnv p s₀ s) :
    DataW (p.2 0) (stOf (p.2 7)) (p.2 7) p.1 1536 s (p.2 5) (p.2 6).toNat :=
  ⟨⟨covers_left h.dIn, G.fd, G.d_w.sub_right (by rw [stOf_w64 G.L.fw]; exact Lay.wSub (by decide)), G.d_w, G.k_d⟩,
    h.dIn, G.c_d⟩

theorem oneCrypt_pc (icb : State → Block) :
    Pc (fun (b : State × State) s => (OEnv p b.1 s ∧
        CtrS s.mem (stOf (p.2 7)) (ctxCiph b.1.mem (w64 (p.2 0))) (icb b.1) 0) ∧ s = b.2) (oneCrypt ci.fn)
      (fun b s' => OEnv p b.1 s' ∧
        bytesAt s'.mem (w64 (p.2 5)) (p.2 6).toNat =
          xorKs (ctxCiph b.1.mem (w64 (p.2 0))) (icb b.1) 0 (bytesAt b.2.mem (w64 (p.2 5)) (p.2 6).toNat) ∧
        Frame (crFrame (stOf (p.2 7)) (p.2 7) p.1 1536 (p.2 5) (p.2 6).toNat) b.2.mem s'.mem) := by
  have L := G.L
  rw [oneCrypt_eq]
  refine Pc.seq (Q := fun b s₁ => OEnv p b.1 s₁ ∧
      CrIn (p.2 0) (stOf (p.2 7)) (p.2 7) p.1 1536 (p.2 5) (p.2 6).toNat 0 s₁ ∧
      CtrS s₁.mem (stOf (p.2 7)) (ctxCiph b.1.mem (w64 (p.2 0))) (icb b.1) 0 ∧
      Frame [pslotR (p.2 7)] b.2.mem s₁.mem)
    (Pc.taint [.ebp] (fun b s ⟨⟨h, hc⟩, hs⟩ => ?_) (fun _ _ s₁ s₂ ⟨⟨h₁, _⟩, _⟩ ⟨⟨h₂, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  · subst hs
    obtain ⟨s', run, d, n, bz, f, bp, si, sp, rd, wr⟩ := setP_ok G (so := dataO) (sl := lenO) (by decide) (by decide)
      (by decide) (by decide) h.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have o' := h.frame G (Frame.oD (pslot_oF f)) bp si sp rd wr
    refine ⟨o', ⟨o'.env, by rw [d]; exact h.dataO, by rw [n, h.lenO, ofNat_toNat32], by rw [bz]; rfl,
      (p.2 6).isLt, dataW_of G o'⟩, ?_, f⟩
    exact hc.congr (blockAt_frame f (st_pslot G (by decide))) (blockAt_frame f (st_pslot G (by decide)))
  refine Pc.mono (Pc.lift (Pc.forall fun (c : Block) => crypt_pc L rfl (D := p.2 5)
    (n := (p.2 6).toNat) (P := 0) (icb := c)) (fun _ s => s.mem) fun b s ⟨_, hi, _⟩ => ⟨hi, rfl⟩)
    (fun _ _ h => h) fun b s' ⟨s₁, ⟨h₁, hi, hc, f⟩, ho, rd, wr⟩ => ?_
  have hco := ho (icb b.1)
  have hf : Frame (⟨w64 (p.2 5), (p.2 6).toNat⟩ :: oF p) s₁.mem s'.mem := hco.frame.sub (crFrame_oF G)
  refine ⟨h₁.frameE G (Frame.oDD hf) hco.env rd wr, ?_, ?_⟩
  · have := hco.out (by rw [h₁.ciph]; exact hc)
    rwa [h₁.ciph, bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact G.d_w.sub_right (Lay.wSub (by decide))) (by have := G.fd; omega_using [])] at this
  · exact (f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wsR (p.2 7), by simp, pslot_ws _⟩).trans hco.frame

theorem tagFrame_oF {o : Nat} : ∀ r ∈ tagFrame (stOf (p.2 7)) (p.2 7) p.1 o,
    ∃ r' ∈ ⟨w64 (p.2 7) + BitVec.ofNat 64 o, 16⟩ :: oF p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have c : ∀ {r : Region}, (∃ r' ∈ oF p, Region.Sub r r') →
      ∃ r' ∈ ⟨w64 (p.2 7) + BitVec.ofNat 64 o, 16⟩ :: oF p, Region.Sub r r' :=
    fun ⟨r', h₁, h₂⟩ => ⟨r', List.mem_cons_of_mem _ h₁, h₂⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact c (st0_sub_oF G (by decide))
  · exact c (w_sub_oF (by decide) (by decide))
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact c ws_sub_oF
  · exact c stk_sub_oF

omit G in
theorem wo_oFF {o : Nat} (ho : o = 0 ∨ o = 112) {m m' : Mem}
    (h : Frame (⟨w64 (p.2 7) + BitVec.ofNat 64 o, 16⟩ :: oF p) m m') : Frame (oFF p) m m' := by
  refine h.sub fun r hr => ?_
  rcases List.mem_cons.mp hr with rfl | hr
  · rcases ho with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by rw [BitVec.add_zero]; exact fun _ h => h⟩
    · exact ⟨⟨w64 (p.2 7) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ h => h⟩

theorem OTIn.pslot {s₀ s s' : State} (h : OTIn p s₀ s) (f : Frame [pslotR (p.2 7)] s.mem s'.mem)
    (bp : s'.gpr .ebp = s.gpr .ebp) (si : s'.gpr .esi = s.gpr .esi) (sp : s'.gpr .esp = s.gpr .esp)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) : OTIn p s₀ s' := by
  have hl : (xA p s₀).length % 16 = 0 := by
    simp only [xA, List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine ⟨h.o.frame G (Frame.oD (pslot_oF f)) bp si sp rd wr, ?_, h.y.congr (blockAt_frame f (st_pslot G
    (by decide))) (by rw [hl]; rfl)⟩
  have e := blockAt_frame f (st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact h.j

theorem st_sub_oT {o d k : Nat} (h : d + k ≤ 48) :
    ∃ r' ∈ oT p o, Region.Sub ⟨w64 (stOf (p.2 7)) + BitVec.ofNat 64 d, k⟩ r' := by
  rw [st_eq G]; exact ⟨_, List.mem_cons_self .., Offset.sub _ (by omega_using []) (by omega_using [h])⟩

theorem st0_sub_oT {o k : Nat} (h : k ≤ 48) : ∃ r' ∈ oT p o, Region.Sub ⟨w64 (stOf (p.2 7)), k⟩ r' := by
  rw [stOf_w64 G.L.fw]; exact ⟨_, List.mem_cons_self .., Offset.sub _ (by omega_using []) (by omega_using [h])⟩

omit G in
theorem pslot_oT {o : Nat} {m m' : Mem} (f : Frame [pslotR (p.2 7)] m m') : Frame (oT p o) m m' :=
  f.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wsR (p.2 7), by simp, pslot_ws _⟩

theorem absFrame_oT {o : Nat} : ∀ r ∈ absFrame (stOf (p.2 7)) (p.2 7) p.1 28 16, ∃ r' ∈ oT p o, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st_sub_oT G (by decide)
  · exact st_sub_oT G (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, G.L.below28⟩

theorem tFrame_oT {o : Nat} : ∀ r ∈ tFrame (stOf (p.2 7)) (p.2 7) p.1 28 16, ∃ r' ∈ oT p o, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact st_sub_oT G (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, G.L.below28⟩

theorem tagFrame_oT {o : Nat} : ∀ r ∈ tagFrame (stOf (p.2 7)) (p.2 7) p.1 o, ∃ r' ∈ oT p o, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact st0_sub_oT G (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

omit G in
theorem oT_oF {o : Nat} {m m' : Mem} (h : Frame (oT p o) m m') :
    Frame (⟨w64 (p.2 7) + BitVec.ofNat 64 o, 16⟩ :: oF p) m m' := by
  refine h.sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨w64 (p.2 7) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨w64 (p.2 7) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The counter block, apart from what `oneTag o` writes. -/
theorem cb_oT {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ oT p o, (⟨w64 (stOf (p.2 7)) + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  rw [st_eq G]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rcases ho with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (G.L.stk_w (by decide)).symm

theorem oneTag_pc {o : Nat} (ho : o = 0 ∨ o = 112) :
    Pc (fun (b : State × State) s => OTIn p b.1 s ∧ s = b.2) (oneTag vg.callees ci.fn o)
      (fun b s' => OEnv p b.1 s' ∧
        bytesAt s'.mem (w64 (p.2 7) + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom (ctxH b.1.mem (w64 (p.2 0))) (ghash (ctxH b.1.mem (w64 (p.2 0)))
            (blocks (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 5)) (p.2 6).toNat ++
              zeros (padLen (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 5)) (p.2 6).toNat).length))))
            [ofBytes (lensBlock (p.2 4).toNat (p.2 6).toNat)] ^^^
            ctxCiph b.1.mem (w64 (p.2 0)) (jOf p b.1)) ∧
        Frame (oT p o) b.2.mem s'.mem) := by
  have L := G.L
  have hl : ∀ s₀, (xA p s₀).length % 16 = 0 := fun s₀ => by
    simp only [xA, List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  rw [oneTag_eq]
  -- The data's arguments.
  refine Pc.seq (Q := fun b s₁ => OTIn p b.1 s₁ ∧
      AbsIn (p.2 0) (stOf (p.2 7)) (p.2 7) p.1 28 (p.2 5) (p.2 6).toNat 0 s₁ ∧
      Frame [pslotR (p.2 7)] b.2.mem s₁.mem)
    (Pc.taint [.ebp] (fun b s ⟨h, hs⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)) ?_
  · subst hs
    obtain ⟨s', run, d, n, bz, f, bp, si, sp, rd, wr⟩ := setP_ok G (so := dataO) (sl := lenO) (by decide) (by decide)
      (by decide) (by decide) h.o.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have h' := h.pslot G f bp si sp rd wr
    exact ⟨h', ⟨h'.o.env, by rw [d]; exact h.o.dataO, by rw [n, h.o.lenO, ofNat_toNat32], by rw [bz]; rfl,
      by decide, (p.2 6).isLt, DataOk.mono (dataW_of G h'.o).ok (by decide) G.L.sp⟩, f⟩
  -- Absorbed.
  refine Pc.seq (Q := fun b s₂ => OEnv p b.1 s₂ ∧
      blockAt s₂.mem (w64 (stOf (p.2 7))) = jOf p b.1 ∧
      Absorbed s₂.mem (w64 (stOf (p.2 7)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 7)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 5)) (p.2 6).toNat) ∧
      Frame (oT p o) b.2.mem s₂.mem)
    (Pc.mono (Pc.lift (absorb_pc L.lay (yo := 16) (.inr rfl) (b := 0) (by decide) (p.2 6).isLt) (fun _ s => s.mem)
      fun b s ⟨_, ha, _⟩ => ⟨ha, rfl⟩) (fun _ _ h => h)
      fun b s₂ ⟨s₁, ⟨h₁, _, f⟩, ho, rd, wr⟩ => ⟨h₁.o.frameE G
        (Frame.oD (ho.frame.sub (absFrame_oF G))) ho.env rd wr, ?_, ?_,
        (pslot_oT f).trans (ho.frame.sub (absFrame_oT G))⟩) ?_
  · have := blockAt_frame ho.frame (st_absFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact h₁.j
  · have := ho.abs (xA p b.1) (hl b.1) (by rw [h₁.o.hk]; exact h₁.y)
    rwa [h₁.o.hk, bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact G.d_w.sub_right (Lay.wSub (by decide))) (by have := G.fd; omega_using [])] at this
  -- `bO`.
  refine Pc.seq (Q := fun b s₃ => OEnv p b.1 s₃ ∧
      blockAt s₃.mem (w64 (stOf (p.2 7))) = jOf p b.1 ∧
      Absorbed s₃.mem (w64 (stOf (p.2 7)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 7)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 5)) (p.2 6).toNat) ∧
      Frame (oT p o) b.2.mem s₃.mem ∧ slotv s₃.mem (p.2 7) bO = BitVec.ofNat 32 ((p.2 6).toNat % 16))
    (Pc.taint [.ebp] (fun b s₂ ⟨h₂, hj, ha, f⟩ => ?_) (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s', run, bz, f', bp, si, sp, rd, wr⟩ := setB_ok G (sl := lenO) (by decide) (by decide) h₂.env
    refine WP.of_runBlock ⟨s', run, ?_⟩
    have hx : (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 5)) (p.2 6).toNat).length % 16 < 16 :=
      Nat.mod_lt _ (by decide)
    refine ⟨h₂.frame G (Frame.oD (pslot_oF f')) bp si sp rd wr, ?_,
      ha.congr (blockAt_frame f' (st_pslot G (by decide))) (bytesAt_frame f' (fun r hr =>
        (st_pslot G (d := 32) (by decide) r hr).sub_left (Region.sub_prefix (by omega_using []))) (by omega_using [])),
      f.trans (pslot_oT f'), by rw [bz, h₂.lenO]⟩
    have e := blockAt_frame f' (st_pslot G (d := 0) (by decide)); rw [BitVec.add_zero] at e; rw [e]; exact hj
  -- Padded.
  refine Pc.seq (Q := fun b s₄ => OEnv p b.1 s₄ ∧
      blockAt s₄.mem (w64 (stOf (p.2 7))) = jOf p b.1 ∧
      Absorbed s₄.mem (w64 (stOf (p.2 7)) + BitVec.ofNat 64 16) (w64 (stOf (p.2 7)) + BitVec.ofNat 64 32)
        (ctxH b.1.mem (w64 (p.2 0))) (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 5)) (p.2 6).toNat ++
          zeros (padLen (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 5)) (p.2 6).toNat).length)) ∧
      Frame (oT p o) b.2.mem s₄.mem)
    (Pc.mono (Pc.lift (flush_pc L.lay (yo := 16) (.inr rfl) (b := (p.2 6).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun _ s => s.mem) fun b s ⟨h, _, _, _, hb⟩ => ⟨⟨h.env, hb⟩, rfl⟩) (fun _ _ h => h)
      fun b s₄ ⟨s₃, ⟨h₃, hj, ha, f, _⟩, ho, rd, wr⟩ => ⟨h₃.frameE G
        (Frame.oD (ho.frame.sub (tFrame_oF G))) ho.env rd wr, ?_, ?_, f.trans (ho.frame.sub (tFrame_oT G))⟩) ?_
  · have := blockAt_frame ho.frame (st_tFrame G (d := 0) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]; exact hj
  · have hx : (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 5)) (p.2 6).toNat).length % 16 = (p.2 6).toNat % 16 := by
      rw [List.length_append, length_bytesAt]; have := hl b.1; omega_using [this]
    have := ho.abs _ hx (by rw [h₃.hk]; exact ha)
    rwa [h₃.hk] at this
  -- The tag.
  refine Pc.mono (Pc.lift (tag_pc L ho (.inr (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)) (alo := p.2 4)
    (ahi := 0) (tlo := p.2 6) (thi := 0)) (fun _ s => s.mem)
    fun b s ⟨h, _, _, _⟩ => ⟨⟨h.env, ⟨h.alO, h.zO, h.lenO, h.zO⟩⟩, rfl⟩) (fun _ _ h => h)
    fun b s₅ ⟨s₄, ⟨h₄, hj, ha, f⟩, ho', rd, wr⟩ => ⟨h₄.frameE G
      (wo_oFF ho (ho'.frame.sub (tagFrame_oF G))) ho'.env rd wr, ?_,
      f.trans (ho'.frame.sub (tagFrame_oT G))⟩
  have hX : (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 5)) (p.2 6).toNat ++
      zeros (padLen (xA p b.1 ++ bytesAt b.2.mem (w64 (p.2 5)) (p.2 6).toNat).length)).length % 16 = 0 := by
    rw [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  rw [ho'.out, h₄.hk, h₄.ciph, hj, Proof.Gcm.Absorbed.whole_eq ha hX]
  simp only [val64, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add]

end

end VG.Proof.Sm4Gcm.X86

end

end

/-!
# SM4-GCM on x86: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. The entry (`oneEntry_pc`),
`J₀` and the additional data (`oneAad_pc`), the data encrypted
(`oneCrypt_pc`), the tag into `W` (`oneTag_pc`) and copied to `tag`
(`tagOut_ok`), and the exit, as one `Pc` (`seal_pc`): correct
(`seal_correct`) and constant time (`seal_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl} {ci : CtrImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen inc32 ghash ghashFrom blocks toBytes ofBytes gctr fullTag encryptWith)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

/-- The padded input of GHASH, as `seal` and `open` absorb it: the
additional data padded, then the data, padded. -/
theorem padded_eq (a c : List Byte) :
    Proof.Gcm.padded a c = a ++ zeros (padLen a.length) ++ c ++
      zeros (padLen (a ++ zeros (padLen a.length) ++ c).length) := by
  by_cases hc : c = []
  · subst hc
    have h0 : padLen (a ++ zeros (padLen a.length)).length = 0 := by
      have := Proof.Gcm.length_pad_mod a.length
      simp only [List.length_append, Proof.Gcm.length_zeros, padLen] at this ⊢; omega_using []
    simp only [Proof.Gcm.padded, Proof.Gcm.ghashInput_nil, List.append_nil, h0]
    simp [zeros]
  · simp only [Proof.Gcm.padded, Proof.Gcm.ghashInput_of_ne hc]

theorem toBytes_take16 (x : Block) : (toBytes x).take 16 = toBytes x :=
  List.take_of_length_le (by rw [Proof.Cmac.toBytes_length])

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

/-- A block of the state before the counter block, apart from what `crypt` writes. -/
theorem st_crFrameO {d : Nat} (hd : d + 16 ≤ 48) :
    ∀ r ∈ crFrame (stOf (p.2 7)) (p.2 7) p.1 1536 (p.2 5) (p.2 6).toNat,
      (⟨w64 (stOf (p.2 7)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (G.d_w.sub_right (by rw [st_eq G]; exact Lay.wSub (by omega_using [hd]))).symm
  · exact Lay.st_st (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact G.L.st_w (by omega_using [hd]) (.inr ⟨by decide, by decide⟩)
  · exact (G.L.stk_st (by omega_using [hd])).symm

/-- The data, apart from the regions of `W` and the stack the pieces write. -/
theorem d_oF : ∀ r ∈ oF p, (⟨w64 (p.2 5), (p.2 6).toNat⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.k_d.symm

theorem d_woF {o : Nat} (ho : o + 16 ≤ 2560) :
    ∀ r ∈ ⟨w64 (p.2 7) + BitVec.ofNat 64 o, 16⟩ :: oF p, (⟨w64 (p.2 5), (p.2 6).toNat⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact G.d_w.sub_right (Lay.wSub ho)
  · exact d_oF G r hr

end

theorem seal_eq : («seal» vg.callees ci.fn) = .seq (oneEntry 8 ([(7, tpO)].flatMap (fun (p : Nat × Nat) => keep p.1 p.2)))
    (.seq (oneAad vg.callees) (.seq (oneCrypt ci.fn) (.seq (oneTag vg.callees ci.fn 0)
      (.seq (tagOut 0) (.block restore))))) := rfl

theorem seal_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => sealPre s₀ ∧ pubSw 9 7 s₀ = p ∧ s = s₀) («seal» vg.callees ci.fn)
      (fun s₀ s' => abiPreserved s₀ s' ∧ sealX86.post s₀ s') := by
  by_cases hex : ∃ s₀, sealPre s₀ ∧ pubSw 9 7 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have G : OL p := (op_of_seal hz).ol rfl (by decide) hzp
  have L := G.L
  have a8 : ∀ {s₀ : State}, pubSw 9 7 s₀ = p → arg s₀ 7 = p.2 8 := fun h => pubSw_last h (by decide) rfl
  have a67 : ∀ {s₀ : State}, pubSw 9 7 s₀ = p → arg s₀ 5 = p.2 5 ∧ arg s₀ 6 = p.2 6 := fun h =>
    ⟨pubSw_arg h (by decide) (by decide) (by decide), pubSw_arg h (by decide) (by decide) (by decide)⟩
  obtain ⟨-, fT, tw, rt, dt⟩ := sealPre_tag hz
  rw [a8 hzp] at fT
  rw [a8 hzp, pubSw_W hzp (m := 8) (by decide) rfl] at tw
  rw [a8 hzp, pubSw_esp hzp] at rt
  rw [a8 hzp, (a67 hzp).1, (a67 hzp).2] at dt
  rw [seal_eq]
  -- The entry, `J₀` and the additional data.
  refine Pc.seq (oneEntry_pc 9 8 rfl (by decide) [(7, tpO)] (by decide) (by decide) (by simp) sealPre
    (fun _ h => op_of_seal h) p G (by taint_decide) (by taint_decide)) ?_
  refine Pc.seq (Pc.lift (oneAad_pc G) (fun s₀ s => (s₀, s)) fun s₀ s h => ⟨h.1, rfl⟩) ?_
  -- The data encrypted.
  refine Pc.seq (Pc.lift (oneCrypt_pc G (fun s₀ => inc32 (jOf p s₀))) (fun s₀ s => (s₀, s))
    fun s₀ s ⟨_, _, ⟨ha, _⟩, _⟩ => ⟨⟨ha.o, Proof.Gcm.ctr_zero _ _ _ _ ha.cb⟩, rfl⟩) ?_
  -- The tag.
  refine Pc.seq (Pc.lift (oneTag_pc G (o := 0) (.inl rfl)) (fun s₀ s => (s₀, s))
    fun s₀ s ⟨s₂, ⟨_, _, ⟨ha, _⟩, _⟩, ⟨o', _, fC⟩, _⟩ => ⟨⟨o', ?_, ?_⟩, rfl⟩) ?_
  · have := blockAt_frame fC (st_crFrameO G (d := 0) (by decide))
    rw [BitVec.add_zero] at this
    rw [this]; exact ha.j
  · have hl : (xA p s₀).length % 16 = 0 := by
      simp only [xA, List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
    exact ha.y.congr (blockAt_frame fC (st_crFrameO G (by decide))) (by rw [hl]; rfl)
  -- The tag copied to `tag`.
  refine Pc.seq (Pc.of (I := fun s => WEnv (p.2 7) s ∧ slotv s.mem (p.2 7) tpO = p.2 8 ∧
      Covers [⟨w64 (p.2 8), 16⟩] s.wr)
    (R := fun s s' => bytesAt s'.mem (w64 (p.2 8)) 16 = bytesAt s.mem (w64 (p.2 7) + BitVec.ofNat 64 0) 16 ∧
      Frame [⟨w64 (p.2 8), 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (fun s hs => tagOut_ok hs.1 (by decide) hs.2.1 hs.2.2 fT) (tagOut_ct rfl fun s hs => ⟨hs.1, hs.2.1⟩) _
    (fun s₀ s ⟨_, ⟨_, ⟨_, ⟨_, _, hpub, hpre⟩, _⟩, _⟩, ⟨o₄, _, _⟩, _⟩ => ⟨⟨o₄.env.ebp, o₄.env.wW, L.fw⟩,
      by rw [o₄.tp, a8 hpub], by rw [o₄.wr, ← a8 hpub]; exact (sealPre_tag hpre).1⟩)) ?_
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s'' ⟨s, ⟨s₃, ⟨s₂, ⟨sE, ⟨hE, _, hpub, _⟩, ⟨_, fA⟩, _⟩, ⟨_, hc, _⟩, _⟩,
      ⟨o₄, ht, fT⟩, _⟩, b, f, bp, si, sp, rd, wr⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, ⟨_, _, ⟨o₁, _⟩, _⟩, _, _, e₁, _⟩ ⟨_, ⟨_, _, ⟨o₂, _⟩, _⟩, _, _, e₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁, e₂, o₁.env.ebp, o₂.env.ebp]) (by taint_decide)
  have esp := pubSw_esp hpub
  have a : ∀ i, i < 7 → arg s₀ i = p.2 i := fun i hi => pubSw_arg hpub (by omega_using [hi]) (by omega_using [hi]) (by omega_using [hi])
  have tS : ∀ r ∈ [(⟨w64 (p.2 8), 16⟩ : Region)], (savedR (p.2 7)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (tw.sub_right (Lay.wSub (by decide))).symm
  have tR : ∀ r ∈ [(⟨w64 (p.2 8), 16⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact rt
  refine WP.mono (exit_ok (W := p.2 7) (by rw [bp, o₄.env.ebp]) (by rw [sp, o₄.env.esp, esp])
    (by rw [rd, wr]; exact covers_left o₄.env.wW) L.fw (o₄.saved.frame f tS)
    (by rw [esp, ret_kept f tR]; exact o₄.ret)) fun s' ⟨abi, m', _, _, _⟩ => ⟨abi, ?_⟩
  have hD₂ : bytesAt s₂.mem (w64 (p.2 5)) (p.2 6).toNat = bytesAt s₀.mem (w64 (p.2 5)) (p.2 6).toNat := by
    rw [bytesAt_frame fA (d_oF G) (by have := G.fd; omega_using [])]; exact hE.data
  have hD₄ : bytesAt s.mem (w64 (p.2 5)) (p.2 6).toNat = bytesAt s₃.mem (w64 (p.2 5)) (p.2 6).toNat :=
    bytesAt_frame (oT_oF fT) (d_woF G (by decide)) (by have := G.fd; omega_using [])
  have hD₅ : bytesAt s''.mem (w64 (p.2 5)) (p.2 6).toNat = bytesAt s.mem (w64 (p.2 5)) (p.2 6).toNat :=
    bytesAt_frame f (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dt) (by have := G.fd; omega_using [])
  have hcg : gctr (ctxCiph s₀.mem (w64 (p.2 0))) (inc32 (jOf p s₀))
      (bytesAt s₀.mem (w64 (p.2 5)) (p.2 6).toNat) = bytesAt s₃.mem (w64 (p.2 5)) (p.2 6).toNat := by
    rw [hc, hD₂, Proof.Gcm.gctr_eq]
  simp only [sealX86]
  rw [a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide), a 5 (by decide),
    a 6 (by decide), a8 hpub, m']
  simp only [encryptWith]
  rw [hcg, hD₅, hD₄, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  rw [b, ht, Proof.Gcm.fullTag_eq, toBytes_take16, padded_eq, length_bytesAt, length_bytesAt]

theorem seal_correct (s : State) (hs : sealX86.pre s) :
    ∃ t s', Exec isa («seal» vg.callees ci.fn) s t s' ∧ abiPreserved s s' ∧ sealX86.post s s' :=
  (seal_pc (pubSw 9 7 s)).wp s s ⟨hs, rfl, rfl⟩

theorem seal_ct : ConstantTime isa sealX86.pre sealX86.pub («seal» vg.callees ci.fn) :=
  Pc.constantTime (pubSw 9 7) (fun _ _ _ _ h => pubSw_eq (by decide) h) seal_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.Sm4Gcm.X86

end

end

/-!
# SM4-GCM on x86: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. The entry (`oneEntry_pc`,
keeping `tag_len` too), the tag length checked (`tagLenOk_pc`), and then
either nothing, or `J₀` and the additional data (`oneAad_pc`), the tag of
the ciphertext into `W + 112` (`oneTag_pc`), the received tag copied
(`recv_ok`) and compared (`cmp_ok`) without a branch, and the data decrypted
(`oneCrypt_pc`) if they are equal, as one `Pc` (`open_pc`): correct
(`open_correct`) and constant time but for whether the tag is right
(`open_ct`), which the contract lets it leak: the index of the `Pc` is the
public data and that bit.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl} {ci : CtrImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen inc32 ghash ghashFrom blocks toBytes ofBytes gctr fullTag openResult decryptWith)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

/-- What `open` computes, in terms of the public data `p`. -/
abbrev oRes (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : Option (List Byte) :=
  openResult (ctxCiph s₀.mem (w64 (p.2 0))) (ctxH s₀.mem (w64 (p.2 0))) (p.2 8).toNat
    (bytesAt s₀.mem (w64 (p.2 1)) (p.2 2).toNat) (bytesAt s₀.mem (w64 (p.2 5)) (p.2 6).toNat)
    (bytesAt s₀.mem (w64 (p.2 3)) (p.2 4).toNat) (bytesAt s₀.mem (w64 (p.2 9)) (p.2 8).toNat)

/-- The arguments of `open`, in its public data (`W` at 8, `tag` at 10). -/
theorem open_arg {s₀ : State} {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubSw 10 7 s₀ = p) {i : Nat}
    (hi : i < 7 ∨ i = 8) : arg s₀ i = p.2 i :=
  pubSw_arg hp (by omega_using [hi]) (by omega_using [hi]) (by omega_using [hi])

theorem open_tag {s₀ : State} {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubSw 10 7 s₀ = p) : arg s₀ 7 = p.2 9 :=
  pubSw_last hp (by decide) rfl

theorem openRes_eq {s₀ : State} {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubSw 10 7 s₀ = p) :
    openRes s₀ = oRes p s₀ := by
  simp only [openRes, oRes, open_arg hp (i := 0) (by decide), open_arg hp (i := 1) (by decide),
    open_arg hp (i := 2) (by decide), open_arg hp (i := 3) (by decide), open_arg hp (i := 4) (by decide),
    open_arg hp (i := 5) (by decide), open_arg hp (i := 6) (by decide),
    open_tag hp, open_arg hp (i := 8) (by decide)]

/-- The tag of the message, and the tag received. -/
abbrev tagOf (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : List Byte :=
  fullTag (ctxCiph s₀.mem (w64 (p.2 0))) (ctxH s₀.mem (w64 (p.2 0)))
    (bytesAt s₀.mem (w64 (p.2 1)) (p.2 2).toNat) (bytesAt s₀.mem (w64 (p.2 3)) (p.2 4).toNat)
    (bytesAt s₀.mem (w64 (p.2 5)) (p.2 6).toNat)

abbrev rcvOf (p : BitVec 32 × (Nat → BitVec 32)) (s₀ : State) : List Byte :=
  bytesAt s₀.mem (w64 (p.2 9)) (p.2 8).toNat

theorem oRes_ok {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (ht : Spec.Gcm.tagLenOk (p.2 8).toNat = true) :
    oRes p s₀ = if (tagOf p s₀).take (p.2 8).toNat = rcvOf p s₀ then
      some (gctr (ctxCiph s₀.mem (w64 (p.2 0))) (inc32 (jOf p s₀))
        (bytesAt s₀.mem (w64 (p.2 5)) (p.2 6).toNat)) else none := by
  simp only [oRes, openResult, ht, ↓reduceIte, decryptWith]

theorem oRes_bad {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (ht : Spec.Gcm.tagLenOk (p.2 8).toNat = false) :
    oRes p s₀ = none := by
  simp only [oRes, openResult, ht, Bool.false_eq_true, ↓reduceIte]

/-- What is fixed of a run of `open` for the index `q`: the public data, and
whether it returns 1. -/
structure IX (q : (BitVec 32 × (Nat → BitVec 32)) × Bool) (s₀ : State) : Prop where
  pre : openPre s₀
  pub : pubSw 10 7 s₀ = q.1
  res : (oRes q.1 s₀).isSome = q.2

theorem IX.q2 {q : (BitVec 32 × (Nat → BitVec 32)) × Bool} {s₀ : State} (h : IX q s₀)
    (ht : Spec.Gcm.tagLenOk (q.1.2 8).toNat = true) :
    q.2 = decide ((tagOf q.1 s₀).take (q.1.2 8).toNat = rcvOf q.1 s₀) := by
  rw [← h.res, oRes_ok ht]
  split <;> simp_all

/-- What `open` returns, before the exit. -/
def PostO (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop :=
  match oRes p s₀ with
  | some pt => s.gpr .eax = 1 ∧ bytesAt s.mem (w64 (p.2 5)) (p.2 6).toNat = pt
  | none => s.gpr .eax = 0 ∧
    bytesAt s.mem (w64 (p.2 5)) (p.2 6).toNat = bytesAt s₀.mem (w64 (p.2 5)) (p.2 6).toNat

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

/-- `OEnt`, after code that keeps the memory and the registers it pins. -/
theorem OEnt.same {s₀ s s' : State} (h : OEnt p s₀ s) (hm : s'.mem = s.mem) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    OEnt p s₀ s' :=
  ⟨h.o.frame G (by rw [hm]; exact Frame.refl _ _) hbp hsi hsp hrd hwr, by rw [hm]; exact h.dO,
    by rw [hm]; exact h.nO, by rw [hm]; exact h.iv, by rw [hm]; exact h.data, by rw [hm]; exact h.frame⟩

/-- A kept slot, apart from the tag at `W + o` and what the pieces write. -/
theorem kept_woF {o n o' : Nat} (h₁ : 128 ≤ o)
    (h₂ : o + n ≤ auxO ∨ (auxO + 4 ≤ o ∧ o + n ≤ rO) ∨ (rO + 16 ≤ o ∧ o + n ≤ 240))
    (ho' : o' + 16 ≤ 128) :
    ∀ r ∈ ⟨w64 (p.2 7) + BitVec.ofNat 64 o', 16⟩ :: oF p,
      (⟨w64 (p.2 7) + BitVec.ofNat 64 o, n⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [auxO, rO] at h₂
    exact Lay.w_w (.inr (by omega_using [h₁, ho'])) (by omega_using [h₂]) (by omega_using [ho'])
  · exact slot_oF G h₁ h₂ r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

omit G in
/-- A region apart from `W` and the stack the calls use, apart from what the pieces write. -/
theorem t_woF {o : Nat} (ho : o + 16 ≤ 2560) {T : Region} (tw : T.Disjoint ⟨w64 (p.2 7), 2560⟩)
    (kt : (below p.1 1536).Disjoint T) : ∀ r ∈ ⟨w64 (p.2 7) + BitVec.ofNat 64 o, 16⟩ :: oF p, T.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact tw.sub_right (Lay.wSub ho)
  · exact tw.sub_right (Lay.wSub (by decide))
  · exact tw.sub_right (Lay.wSub (by decide))
  · exact tw.sub_right (Lay.wSub (by decide))
  · exact tw.sub_right (Lay.wSub (by decide))
  · exact kt.symm

/-- The counter block, apart from a part of `W` from `W + 80` on. -/
theorem st48_w {o k : Nat} (h : 80 ≤ o) (hk : o + k ≤ 2560) :
    (⟨w64 (stOf (p.2 7)) + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨w64 (p.2 7) + BitVec.ofNat 64 o, k⟩ := by
  rw [st_eq G]; exact Lay.w_w (.inl (by omega_using [h])) (by decide) hk

end

/-- After the received tag is compared and the result kept at `W + auxO`. -/
structure OC (q : (BitVec 32 × (Nat → BitVec 32)) × Bool) (s₀ s : State) : Prop where
  o : OEnv q.1 s₀ s
  ix : IX q s₀
  aux : slotv s.mem (q.1.2 7) auxO = BitVec.ofNat 32 (if q.2 = true then 1 else 0)
  zf : s.zf = some (!q.2)
  cb : blockAt s.mem (w64 (stOf (q.1.2 7)) + BitVec.ofNat 64 48) = inc32 (jOf q.1 s₀)
  data : bytesAt s.mem (w64 (q.1.2 5)) (q.1.2 6).toNat = bytesAt s₀.mem (w64 (q.1.2 5)) (q.1.2 6).toNat

/-- After the data is decrypted if the tag is right. -/
structure OD (q : (BitVec 32 × (Nat → BitVec 32)) × Bool) (s₀ s : State) : Prop where
  o : OEnv q.1 s₀ s
  ix : IX q s₀
  aux : slotv s.mem (q.1.2 7) auxO = BitVec.ofNat 32 (if q.2 = true then 1 else 0)
  data : bytesAt s.mem (w64 (q.1.2 5)) (q.1.2 6).toNat = if q.2 = true then
    gctr (ctxCiph s₀.mem (w64 (q.1.2 0))) (inc32 (jOf q.1 s₀))
      (bytesAt s₀.mem (w64 (q.1.2 5)) (q.1.2 6).toNat) else bytesAt s₀.mem (w64 (q.1.2 5)) (q.1.2 6).toNat

theorem open_eq : («open» vg.callees ci.fn) = .seq (oneEntry 9 ([(7, tpO), (8, tglO)].flatMap
    (fun (p : Nat × Nat) => keep p.1 p.2))) (.seq tagLenOk (.seq (.ite .e (.block [.mov .eax (imm 0)])
    (.seq (oneAad vg.callees) (.seq (oneTag vg.callees ci.fn uO) (.seq recv (.seq (cmp uO)
      (.seq (.block [.store (at_ .ebp auxO) .eax, .alu .test .eax (.reg .eax)])
      (.seq (.ite .e (.block []) (oneCrypt ci.fn)) (.block [.mov .eax (slot auxO)]))))))))
    (.block restore))) := rfl

theorem open_pc (q : (BitVec 32 × (Nat → BitVec 32)) × Bool) :
    Pc (fun (s₀ : State) s => openPre s₀ ∧ (pubSw 10 7 s₀, (openRes s₀).isSome) = q ∧ s = s₀) («open» vg.callees ci.fn)
      (fun s₀ s' => abiPreserved s₀ s' ∧ openX86.post s₀ s') := by
  by_cases hex : ∃ s₀, openPre s₀ ∧ (pubSw 10 7 s₀, (openRes s₀).isSome) = q
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzq⟩ := hex
  obtain hzp : pubSw 10 7 z = q.1 := by rw [← hzq]
  obtain G : OL q.1 := (op_of_open hz).ol rfl (by decide) hzp
  have L := G.L
  obtain ⟨-, ftg, tw, kt⟩ := openPre_tag hz
  rw [open_tag hzp, open_arg hzp (i := 8) (by decide)] at ftg
  rw [open_tag hzp, open_arg hzp (i := 8) (by decide), pubSw_W hzp (m := 9) (by decide) rfl] at tw
  rw [open_tag hzp, open_arg hzp (i := 8) (by decide), pubSw_esp hzp] at kt
  obtain ht32 : (q.1.2 8).toNat < 2 ^ 32 := (q.1.2 8).isLt
  generalize hok : Spec.Gcm.tagLenOk (q.1.2 8).toNat = ok
  rw [open_eq]
  -- The entry.
  refine Pc.seq (Pc.mono (oneEntry_pc 10 9 rfl (by decide) [(7, tpO), (8, tglO)] (by decide) (by decide) (by simp)
    (fun s₀ => openPre s₀ ∧ (openRes s₀).isSome = q.2) (fun _ h => op_of_open h.1) q.1 G (by taint_decide)
    (by taint_decide))
    (fun s₀ s ⟨h₁, hq, hs⟩ => ⟨⟨h₁, by rw [← hq]⟩, by rw [← hq], hs⟩) (fun _ _ h => h)) ?_
  -- The tag length.
  refine Pc.seq (Q := fun s₀ s => OEnt q.1 s₀ s ∧
      slotv s.mem (q.1.2 7) tglO = BitVec.ofNat 32 (q.1.2 8).toNat ∧ IX q s₀ ∧ s.zf = some (!ok))
    (Pc.mono (Pc.lift (tagLenOk_pc (W := q.1.2 7) ht32) (fun _ s => s) fun s₀ s ⟨h, ht, hp, _⟩ =>
      ⟨rfl, h.o.env.ebp, L.aW (by decide), h.o.env.wIn' (by decide), by
        rw [ht (8, tglO) (by simp), open_arg hp (i := 8) (by decide), ofNat_toNat32]⟩) (fun _ _ h => h)
      fun s₀ s ⟨s₁, ⟨h, ht, hp, hpre, hres⟩, ⟨tl, hzf⟩, _, _⟩ =>
        ⟨h.same G tl.mem (tl.other _ (by decide) (by decide)) (tl.other _ (by decide) (by decide))
          (tl.other _ (by decide) (by decide)) tl.rd tl.wr,
          by rw [tl.mem, ht (8, tglO) (by simp), open_arg hp (i := 8) (by decide), ofNat_toNat32],
          ⟨hpre, hp, by rw [← openRes_eq hp]; exact hres⟩, by rw [hzf, hok]⟩) ?_
  refine Pc.seq (Q := fun s₀ s => OEnv q.1 s₀ s ∧ IX q s₀ ∧ PostO q.1 s₀ s)
    (Pc.ite (!ok) (fun _ _ h => h.2.2.2) (fun hb => ?_) (fun hb => ?_)) ?_
  -- A tag length `tagLenOk` does not allow.
  · have hf : ok = false := by simpa using hb
    refine Pc.taint [.ebp] (fun s₀ s ⟨h, _, hx, _⟩ => WP.of_runBlock ⟨_, by xrun [], ?_⟩)
      (fun _ _ s₁ s₂ ⟨h₁, _⟩ ⟨h₂, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)
    refine ⟨h.o.frame G (by mems []; exact Frame.refl _ _) (by regs []) (by regs []) (by regs []) (by mems [])
      (by mems []), hx, ?_⟩
    simp only [PostO, oRes_bad (show Spec.Gcm.tagLenOk (q.1.2 8).toNat = false by rw [hok, hf])]
    exact ⟨by regs []; rfl, by mems []; exact h.data⟩
  -- An allowed one.
  obtain hT : ok = true := by simpa using hb
  obtain hT' : Spec.Gcm.tagLenOk (q.1.2 8).toNat = true := by rw [hok, hT]
  obtain ht' : 1 ≤ (q.1.2 8).toNat ∧ (q.1.2 8).toNat ≤ 16 := by
    have := hT'
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at this
    omega_using [this]
  obtain ⟨t1, t16⟩ := ht'
  -- `J₀` and the additional data; the tag of the ciphertext.
  refine Pc.seq (Pc.lift (oneAad_pc G) (fun s₀ s => (s₀, s)) fun s₀ s h => ⟨h.1, rfl⟩) ?_
  refine Pc.seq (Pc.lift (oneTag_pc G (o := 112) (.inr rfl)) (fun s₀ s => (s₀, s))
    fun s₀ s ⟨_, _, ⟨ha, _⟩, _⟩ => ⟨⟨ha.o, ha.j, ha.y⟩, rfl⟩) ?_
  -- The received tag copied.
  obtain tgl : ∀ {sA s₂ s₃ : State}, slotv sA.mem (q.1.2 7) tglO = BitVec.ofNat 32 (q.1.2 8).toNat →
      Frame (oF q.1) sA.mem s₂.mem → Frame (oT q.1 112) s₂.mem s₃.mem →
      slotv s₃.mem (q.1.2 7) tglO = BitVec.ofNat 32 (q.1.2 8).toNat := fun hs fA fT => by
    rw [slotv_eq, slot_frame (oT_oF fT) (kept_woF G (o := tglO) (by decide) (.inl (by decide)) (by decide)),
      slot_frame fA fun r hr => slot_oF G (o := tglO) (by decide) (.inl (by decide)) r
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)), ← slotv_eq]
    exact hs
  refine Pc.seq (Pc.of (I := fun s => WEnv (q.1.2 7) s ∧
      slotv s.mem (q.1.2 7) tglO = BitVec.ofNat 32 (q.1.2 8).toNat ∧ slotv s.mem (q.1.2 7) tpO = q.1.2 9 ∧
      Covers [⟨w64 (q.1.2 9), (q.1.2 8).toNat⟩] (s.rd ++ s.wr))
    (R := fun s s' => bytesAt s'.mem (w64 (q.1.2 7) + BitVec.ofNat 64 rO) 16 =
        bytesAt s.mem (w64 (q.1.2 9)) (q.1.2 8).toNat ++ zeros (16 - (q.1.2 8).toNat) ∧
      Frame [⟨w64 (q.1.2 7) + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (fun s hs => recv_ok hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 ftg tw t1 t16)
    (recv_ct fun s hs => ⟨hs.1, hs.2.1, hs.2.2.1⟩) _
    (fun s₀ s₃ ⟨s₂, ⟨sA, ⟨_, hs, hx, _⟩, ⟨_, fA⟩, _⟩, ⟨o₃, _, fT⟩, _⟩ =>
      ⟨⟨o₃.env.ebp, o₃.env.wW, L.fw⟩, tgl hs fA fT, by rw [o₃.tp, open_tag hx.pub], by
        rw [o₃.rd, o₃.wr, ← open_tag hx.pub, ← open_arg hx.pub (i := 8) (by decide)]
        exact (openPre_tag hx.pre).1⟩)) ?_
  -- Compared.
  obtain rR_tgl : ∀ {s s' : State}, Frame [⟨w64 (q.1.2 7) + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem →
      slotv s'.mem (q.1.2 7) tglO = slotv s.mem (q.1.2 7) tglO := fun f => by
    rw [slotv_eq, slotv_eq]
    exact slot_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine Pc.seq (Pc.of (I := fun s => WEnv (q.1.2 7) s ∧
      slotv s.mem (q.1.2 7) tglO = BitVec.ofNat 32 (q.1.2 8).toNat)
    (R := fun s s' => s'.gpr .eax = BitVec.ofNat 32
        (if bytesAt s.mem (w64 (q.1.2 7) + BitVec.ofNat 64 uO) (q.1.2 8).toNat ++ zeros (16 - (q.1.2 8).toNat) =
            bytesAt s.mem (w64 (q.1.2 7) + BitVec.ofNat 64 rO) 16 then 1 else 0) ∧
      Frame [⟨w64 (q.1.2 7) + BitVec.ofNat 64 vO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (fun s hs => cmp_ok hs.1 hs.2 t1 t16 (by decide)) (cmp_ct (.inr rfl) fun s hs => hs) _
    (fun s₀ s₄ ⟨s₃, ⟨s₂, ⟨sA, ⟨_, hs, _⟩, ⟨_, fA⟩, _⟩, ⟨o₃, _, fT⟩, _⟩, ⟨_, f₄, bp₄, _, _, _, wr₄⟩⟩ =>
      ⟨⟨by rw [bp₄, o₃.env.ebp], by rw [wr₄]; exact o₃.env.wW, L.fw⟩, by rw [rR_tgl f₄]; exact tgl hs fA fT⟩)) ?_
  -- The result kept, and tested.
  refine Pc.seq (Q := OC q) (Pc.taint [.ebp] (fun s₀ s₅ hk => ?_)
    (fun _ _ s₁ s₂ ⟨_, ⟨_, ⟨_, _, ⟨o₁, _⟩, _⟩, _, _, e₁, _⟩, _, _, e₁', _⟩
      ⟨_, ⟨_, ⟨_, _, ⟨o₂, _⟩, _⟩, _, _, e₂, _⟩, _, _, e₂', _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁', e₁, e₂', e₂, o₁.env.ebp, o₂.env.ebp])
    (by taint_decide)) ?_
  · obtain ⟨s₄, ⟨s₃, ⟨s₂, ⟨sA, ⟨hE, _, hx, _⟩, ⟨ha, fA⟩, _⟩, ⟨o₃, ht, fT⟩, _⟩,
      ⟨b₄, f₄, bp₄, si₄, sp₄, rd₄, wr₄⟩⟩, ⟨a₅, f₅, bp₅, si₅, sp₅, rd₅, wr₅⟩⟩ := hk
    obtain fo₄ : Frame (oF q.1) s₃.mem s₄.mem := f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    obtain fo₅ : Frame (oF q.1) s₄.mem s₅.mem := f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wsR (q.1.2 7), by simp, Offset.sub _ (by decide) (by decide)⟩
    obtain o₅ := (o₃.frame G (Frame.oD fo₄) bp₄ si₄ sp₄ rd₄ wr₄).frame G (Frame.oD fo₅) bp₅ si₅ sp₅ rd₅ wr₅
    -- The tags.
    obtain hc₂ : bytesAt s₂.mem (w64 (q.1.2 5)) (q.1.2 6).toNat = bytesAt s₀.mem (w64 (q.1.2 5)) (q.1.2 6).toNat := by
      rw [bytesAt_frame fA (d_oF G) (by have := G.fd; omega_using [])]; exact hE.data
    obtain hT₃ : bytesAt s₃.mem (w64 (q.1.2 7) + BitVec.ofNat 64 uO) 16 = tagOf q.1 s₀ := by
      dsimp only at ht
      rw [ht, hc₂, tagOf, Proof.Gcm.fullTag_eq, padded_eq, length_bytesAt, length_bytesAt]
    obtain hT₄ : bytesAt s₄.mem (w64 (q.1.2 7) + BitVec.ofNat 64 uO) (q.1.2 8).toNat =
        (tagOf q.1 s₀).take (q.1.2 8).toNat := by
      rw [← bytesAt_take _ _ t16, bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), hT₃]
    obtain hw₃ : bytesAt s₃.mem (w64 (q.1.2 9)) (q.1.2 8).toNat = rcvOf q.1 s₀ := by
      obtain ht₁ : (q.1.2 8).toNat ≤ 2 ^ 64 := by omega_using []
      rw [bytesAt_frame (oT_oF fT) (t_woF (by decide) tw kt) ht₁,
        bytesAt_frame fA (fun r hr => t_woF (o := 0) (by decide) tw kt r (List.mem_cons_of_mem _ hr)) ht₁,
        bytesAt_frame hE.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact tw.sub_right (Lay.wSub (by decide))) ht₁]
    obtain hR₄ : bytesAt s₄.mem (w64 (q.1.2 7) + BitVec.ofNat 64 rO) 16 =
        rcvOf q.1 s₀ ++ zeros (16 - (q.1.2 8).toNat) := by
      rw [b₄, hw₃]
    obtain hq2 := hx.q2 hT'
    obtain a₅' : s₅.gpr .eax = BitVec.ofNat 32 (if q.2 = true then 1 else 0) := by
      rw [a₅, hT₄, hR₄, hq2]
      by_cases h : (tagOf q.1 s₀).take (q.1.2 8).toNat = rcvOf q.1 s₀
      · simp only [h, List.append_left_inj, decide_true, ↓reduceIte]
      · simp only [h, List.append_left_inj, decide_false, Bool.false_eq_true, ↓reduceIte]
    obtain aW := o₅.env.wIn (d := auxO) (n := 4) (by decide)
    refine WP.of_runBlock ⟨_, by xrun [o₅.env.ebp, L.aW, aW], ?_⟩
    obtain fx : Frame (oF q.1) s₅.mem (s₅.mem.writeW (w64 (q.1.2 7) + BitVec.ofNat 64 auxO) (s₅.gpr .eax)) :=
      (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    obtain fx₁ : Frame [⟨w64 (q.1.2 7) + BitVec.ofNat 64 auxO, 4⟩] s₅.mem
        (s₅.mem.writeW (w64 (q.1.2 7) + BitVec.ofNat 64 auxO) (s₅.gpr .eax)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    obtain sg : ∀ {o : Nat}, 80 ≤ o → o + 16 ≤ 2560 → ∀ r ∈ [(⟨w64 (q.1.2 7) + BitVec.ofNat 64 o, 16⟩ : Region)],
        (⟨w64 (stOf (q.1.2 7)) + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact st48_w G h₁ h₂
    refine ⟨o₅.frame G (by mems []; exact Frame.oD fx) (by regs []) (by regs []) (by regs []) (by mems [])
      (by mems []), hx, by mems [slotv_eq]; exact a₅', ?_, ?_, ?_⟩
    · mems []
      rw [a₅']
      cases q.2 <;> rfl
    · mems []
      rw [blockAt_frame fx₁ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact st48_w G (by decide) (by decide),
        blockAt_frame f₅ (sg (by decide) (by decide)), blockAt_frame f₄ (sg (by decide) (by decide)),
        blockAt_frame fT (cb_oT G (.inr rfl))]
      exact ha.cb
    · mems []
      rw [bytesAt_frame fx₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact G.d_w.sub_right (Lay.wSub (by decide)))
          (by have := G.fd; omega_using []),
        bytesAt_frame fo₅ (d_oF G) (by have := G.fd; omega_using []), bytesAt_frame fo₄ (d_oF G) (by have := G.fd; omega_using []),
        bytesAt_frame (oT_oF fT) (d_woF G (by decide)) (by have := G.fd; omega_using [])]
      exact hc₂
  -- The data decrypted if the tags are equal.
  refine Pc.seq (Q := OD q) (Pc.ite (!q.2) (fun _ _ h => h.zf) (fun hb => ?_) (fun hb => ?_)) ?_
  · have hf : q.2 = false := by simpa using hb
    refine Pc.mono Pc.nil (fun _ _ h => h) fun s₀ s h => ⟨h.o, h.ix, h.aux, ?_⟩
    rw [hf]; exact h.data
  · have ht : q.2 = true := by simpa using hb
    refine Pc.mono (Pc.lift (oneCrypt_pc G (fun s₀ => inc32 (jOf q.1 s₀))) (fun s₀ s => (s₀, s))
      fun s₀ s h => ⟨⟨h.o, Proof.Gcm.ctr_zero _ _ _ _ h.cb⟩, rfl⟩) (fun _ _ h => h)
      fun s₀ s' ⟨s, h, ⟨o', hd, fC⟩, _⟩ => ⟨o', h.ix, ?_, ?_⟩
    · rw [slotv_eq, slot_frame fC fun r hr => ?_, ← slotv_eq]
      · exact h.aux
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (G.d_w.sub_right (Lay.wSub (by decide))).symm
        · rw [st_eq G]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w (by decide)).symm
    · rw [hd, h.data, ht, Proof.Gcm.gctr_eq]; rfl
  -- The result.
  refine Pc.taint [.ebp] (fun s₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.o.env.ebp, h₂.o.env.ebp]) (by taint_decide)
  obtain aR := h.o.env.wIn' (d := auxO) (n := 4) (by decide)
  have hv := h.aux
  rw [slotv_eq] at hv
  simp only [auxO] at hv aR
  refine WP.of_runBlock ⟨_, by xrun [h.o.env.ebp, L.aW, aR, hv], ?_⟩
  refine ⟨h.o.frame G (by mems []; exact Frame.refl _ _) (by regs []) (by regs []) (by regs []) (by mems [])
    (by mems []), h.ix, ?_⟩
  obtain hq2 := h.ix.q2 hT'
  simp only [PostO, oRes_ok hT']
  by_cases hX : (tagOf q.1 s₀).take (q.1.2 8).toNat = rcvOf q.1 s₀
  · have h2 : q.2 = true := by rw [hq2]; simpa using hX
    have := h.data
    rw [h2] at this
    simp only [hX, ↓reduceIte, h2]
    exact ⟨by regs []; rfl, by mems []; simpa using this⟩
  · have h2 : q.2 = false := by rw [hq2]; simpa using hX
    have := h.data
    rw [h2] at this
    simp only [hX, ↓reduceIte, h2]
    exact ⟨by regs []; rfl, by mems []; simpa using this⟩
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s ⟨o, hx, hpost⟩ => ?_) (fun _ _ s₁ s₂ ⟨o₁, _⟩ ⟨o₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [o₁.env.ebp, o₂.env.ebp]) (by taint_decide)
  obtain esp := pubSw_esp hx.pub
  refine WP.mono (exit_ok o.env.ebp (by rw [o.env.esp, esp]) (covers_left o.env.wW) L.fw o.saved
    (by rw [esp]; exact o.ret)) fun s' ⟨abi, m', ax, _, _⟩ => ⟨abi, ?_⟩
  simp only [openX86, ret32_eq]
  rw [openRes_eq hx.pub, open_arg hx.pub (i := 5) (by decide), open_arg hx.pub (i := 6) (by decide), m', ax]
  exact hpost

theorem open_correct (s : State) (hs : openX86.pre s) :
    ∃ t s', Exec isa («open» vg.callees ci.fn) s t s' ∧ abiPreserved s s' ∧ openX86.post s s' :=
  (open_pc (pubSw 10 7 s, (openRes s).isSome)).wp s s ⟨hs, rfl, rfl⟩

theorem open_ct : ConstantTime isa openX86.pre openX86.pub («open» vg.callees ci.fn) :=
  Pc.constantTime (fun s => (pubSw 10 7 s, (openRes s).isSome))
    (fun _ _ _ _ h => by rw [pubSw_eq (by decide) h.1, h.2]) open_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.Sm4Gcm.X86
