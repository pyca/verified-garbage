module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixOk
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall

/-!
# AES-GCM `seal_split` on x86-64: what a prefix leaves

Untrusted: everything here is checked by Lean. `PPostG … q` is what the code
before `body` leaves for any number `q` of whole blocks it encrypts: the
first `16 q` bytes of the plaintext `src[0..sl] ‖ dst[sl..len]`
(`splitPt`) encrypted at `dst` from the counter block and absorbed, the rest
of the plaintext after them, and the data from them on kept. `prefix`
leaves it for `q = ⌊sl / 16⌋` (`PPost.toG`, `prefixOk`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)
open VG.Proof.Gcm (Ctr xorKs)

/-- The plaintext of `seal_split` in `m`: the `sl` bytes at `S`, then the
data from byte `sl` on. -/
abbrev splitPt (m : Mem) (D S : Addr) (n sl : Nat) : List Byte := bytesAt m S sl ++ (bytesAt m D n).drop sl

/-- What the code before `body` may write: the counter block, `Y`, the data,
the working space of the calls, `dataO`–`auxO` and the 56 bytes below `SP`. -/
abbrev ppListG (W D SP : Addr) (n : Nat) : List Region :=
  [cbR W, yR W, ⟨D, n⟩, scR W, ⟨W + BitVec.ofNat 64 200, 24⟩, below SP 56]

/-- What the code before `body` leaves, `q` whole blocks of the plaintext
encrypted. -/
structure PPostG (Ctx W SP D S : Addr) (R n sl q : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  le : 16 * q ≤ n
  frame : Frame (ppListG W D SP n) s.mem s'.mem
  enc : bytesAt s'.mem D (16 * q) =
    xorKs (ciphOf s.mem Ctx R) (blockAt s.mem (cbA W)) 0 ((splitPt s.mem D S n sl).take (16 * q))
  ctr : blockAt s'.mem (cbA W) = Nat.repeat inc32 q (blockAt s.mem (cbA W))
  y : blockAt s'.mem (yA W) = ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (yA W)) (blocksAt s'.mem D q)
  tail : bytesAt s'.mem (D + BitVec.ofNat 64 (16 * q)) (n - 16 * q) = (splitPt s.mem D S n sl).drop (16 * q)
  dat : s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * q)
  len : s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * q)
  aux : s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n

/-- Code before `body` that leaves `PPostG` for `q n sl` blocks, a number
the lengths alone give. -/
def PreOk (M : CtxMode) (pre : Prog isa) (q : Nat → Nat → Nat) : Prop :=
  ∀ {Ctx W SP D S : Addr} {R n sl : Nat} {s : State}, PP M Ctx W SP D S R n sl s →
    WP isa pre s (PPostG Ctx W SP D S R n sl (q n sl) s)

/-- A region apart from `W`, the data and the 56 bytes below `SP` is apart
from what the code before `body` writes. -/
theorem pp_outG {W D SP : Addr} {n : Nat} {X : Region} (xw : X.Disjoint ⟨W, 2560⟩)
    (xd : X.Disjoint ⟨D, n⟩) (xs : X.Disjoint (below SP 56)) : ∀ r ∈ ppListG W D SP n, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact xw.sub_right (fun a hc => st_w a (cb_sub a hc))
  · exact xw.sub_right (fun a hc => st_w a (y_sub a hc))
  · exact xd
  · exact xw.sub_right sc_w
  · exact xw.sub_right (Lay.wSub (by decide))
  · exact xs

/-- A slot of `W` before the counter blocks, between the saved registers and
`dataO`, or between `auxO` and the call's working space, is apart from what
the code before `body` writes. -/
theorem pp_wG {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {D : Addr} {n d k : Nat}
    (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (kw : (below SP 56).Disjoint ⟨W, 2560⟩)
    (h : d + k ≤ 32 ∨ (128 ≤ d ∧ d + k ≤ 200) ∨ (224 ≤ d ∧ d + k ≤ 448)) :
    ∀ r ∈ ppListG W D SP n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ ⟨W, 2560⟩ := Lay.wSub (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · show Region.Disjoint _ ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩
    rw [add_ofNat_assoc]; exact L.w_w (by omega) (by omega) (by decide)
  · show Region.Disjoint _ ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩
    rw [add_ofNat_assoc]; exact L.w_w (by omega) (by omega) (by decide)
  · exact (hD.sub_right hs).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact L.w_w (by omega) (by omega) (by decide)
  · exact (kw.sub_right hs).symm

theorem bytesAt_take' (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) : (bytesAt m p n).take k = bytesAt m p k := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem bytesAt_drop' (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    (bytesAt m p n).drop k = bytesAt m (p + BitVec.ofNat 64 k) (n - k) := by
  rw [show n = k + (n - k) by omega, bytesAt_add, Nat.add_sub_cancel_left,
    List.drop_left' (length_bytesAt _ _ _)]

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {s : State} (h : PP M Ctx W SP D S R n sl s)
include h

/-- `prefix` leaves `PPostG` for `q = ⌊sl / 16⌋`. -/
theorem PPost.toG {s' : State} (Q : PPost Ctx W SP D S R n sl s s') : PPostG Ctx W SP D S R n sl (sl / 16) s s' := by
  have hsl := h.sl_le
  have hn := h.data.ok.lt
  have hq : 16 * (sl / 16) ≤ sl := Nat.mul_div_le sl 16
  have pt₁ : (splitPt s.mem D S n sl).take (16 * (sl / 16)) = bytesAt s.mem S (16 * (sl / 16)) := by
    rw [List.take_append_of_le_length (by rw [length_bytesAt]; exact hq), bytesAt_take' _ _ hq]
  have pt₂ : (splitPt s.mem D S n sl).drop (16 * (sl / 16)) =
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) ++
        bytesAt s.mem (D + BitVec.ofNat 64 sl) (n - sl) := by
    rw [List.drop_append_of_le_length (by rw [length_bytesAt]; exact hq), bytesAt_drop' _ _ hq,
      bytesAt_drop' _ _ hsl, show sl - 16 * (sl / 16) = sl % 16 by omega]
  have hqr : 16 * (sl / 16) + sl % 16 = sl := by omega
  refine ⟨Q.env, Q.rd, Q.wr, by omega, Q.frame.sub fun r hr => ?_, ?_, Q.ctr, Q.y, ?_, Q.dat, Q.len, Q.aux⟩
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [pt₁]
    exact (Proof.Gcm.ctr_wholeTo (m := s.mem) (m' := s'.mem) (cb := cbA W) (ks := W) (sp := S) (dp := D)
      (ciph := ciphOf s.mem Ctx R) (icb := blockAt s.mem (cbA W)) (n := 0) (nb := sl / 16)
      ⟨rfl, fun h => (h rfl).elim⟩ rfl Q.blocks Q.ctr).1
  · have eD' : D + BitVec.ofNat 64 (16 * (sl / 16)) + BitVec.ofNat 64 (sl % 16) = D + BitVec.ofNat 64 sl := by
      rw [add_ofNat_assoc, hqr]
    have sR : Region.Sub ⟨D + BitVec.ofNat 64 sl, n - sl⟩ ⟨D, n⟩ := Offset.sub_base D (by omega)
    rw [show n - 16 * (sl / 16) = sl % 16 + (n - sl) by omega, bytesAt_add, eD', Q.tail, pt₂]
    congr 1
    have dw := h.data.ok.w.sub_left sR
    exact bytesAt_frame Q.frame (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl
      · exact dw.sub_right (fun a hc => st_w a (cb_sub a hc))
      · exact dw.sub_right (fun a hc => st_w a (y_sub a hc))
      · exact Offset.disjoint_base D (by omega) (by omega)
      · exact dw.sub_right sc_w
      · exact Offset.disjoint D (.inr (by omega)) (by omega) (by omega)
      · exact dw.sub_right (Lay.wSub (by decide))
      · exact (h.kd.sub_right sR).symm) (by omega)

end

/-- `prefix` meets `PreOk`. -/
theorem prefixOk {M : CtxMode} (T : BlkToFn M) : PreOk M (SealSplit.prefix T.fn) fun _ sl => sl / 16 :=
  fun h => WP.mono (prefix_ok h T) fun _ Q => Q.toG h

end VG.Proof.AesGcm.X86_64.Split
