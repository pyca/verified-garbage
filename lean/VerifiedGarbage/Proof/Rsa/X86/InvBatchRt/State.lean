module

import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Rows
public import VerifiedGarbage.Proof.Divstep.Alg32Def
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Divstep.BatchBasic
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
public import VerifiedGarbage.Proof.Weierstrass.Unch

/-! # The state carried between batches at a run-time width

`StateAt`, `RowInput` and `GcdBatch.MatrixAt` with the divstep window at the header's
`win` rather than in array 3.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass

/-- A batch's transition matrix in the window. -/
structure MatrixAt (B : Addr) (T : Divstep.MSt) (s : State) : Prop where
  d : s.mem.readW (off B win) 32 = BitVec.ofInt 32 T.d
  u : s.mem.readW (off B (win + 12)) 32 = BitVec.ofInt 32 T.u
  v : s.mem.readW (off B (win + 16)) 32 = BitVec.ofInt 32 T.v
  q : s.mem.readW (off B (win + 20)) 32 = BitVec.ofInt 32 T.q
  r : s.mem.readW (off B (win + 24)) 32 = BitVec.ofInt 32 T.r

/-- The encoded inversion state between batches. -/
structure StateAt (len : Nat) (B : Addr) (p iv : Nat) (st : Divstep.W32.IState) (s : State) : Prop where
  d : s.mem.readW (off B win) 32 = BitVec.ofInt 32 st.d
  modulus : val32 s.mem B (rv (kw len) mo) (nw len) = p
  inverse : w32 s.mem B (win + 28) = iv
  f : (val32 s.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
    st.f % 2 ^ (32 * (nw len + 1))
  g : (val32 s.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
    st.g % 2 ^ (32 * (nw len + 1))
  ca : (val32 s.mem B (rv (kw len) (a 6)) (nw len) : Int) = st.a
  cb : (val32 s.mem B (rv (kw len) (a 7)) (nw len) : Int) = st.b
  aTop : w32 s.mem B (rv (kw len) (a 6) + 4 * nw len) = 0
  bTop : w32 s.mem B (rv (kw len) (a 7) + 4 * nw len) = 0

/-- What the matrix rows read. -/
structure RowInput (len : Nat) (B : Addr) (p iv : Nat) (T : Divstep.MSt) (st : Divstep.W32.IState)
    (s : State) : Prop where
  matrix : MatrixAt B T s
  modulus : val32 s.mem B (rv (kw len) mo) (nw len) = p
  inverse : w32 s.mem B (win + 28) = iv
  f : (val32 s.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
    st.f % 2 ^ (32 * (nw len + 1))
  g : (val32 s.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
    st.g % 2 ^ (32 * (nw len + 1))
  ca : (val32 s.mem B (rv (kw len) (a 6)) (nw len) : Int) = st.a
  cb : (val32 s.mem B (rv (kw len) (a 7)) (nw len) : Int) = st.b

/-- The state after a batch with the matrix `T`. -/
def nextState (p iv : Nat) (T : Divstep.MSt) (st : Divstep.W32.IState) : Divstep.W32.IState :=
  ⟨T.d, (T.u * st.f + T.v * st.g) / 2 ^ 30, (T.q * st.f + T.r * st.g) / 2 ^ 30,
    Divstep.W32.mred p iv (T.u * st.a + T.v * st.b), Divstep.W32.mred p iv (T.q * st.a + T.r * st.b)⟩

/-- What the rows write: arrays 0 and 1, 11 to 14, and the sign slot. -/
def rowWrites (len : Nat) : List (Nat × Nat) :=
  [(rv (kw len) (a 0), 2 * (8 * nw len + 8)), (rv (kw len) (a 11), 4 * (8 * nw len + 8)), (signSlot, 4)]

variable {L : Lay} {Z N : Nat}

theorem RowInput.keep {s t : State} {B : Addr} {len p iv : Nat} {T : Divstep.MSt} {st : Divstep.W32.IState}
    (h : RowInput len B p iv T st s) (hb : Bx L s B Z len N) (O : Unch B (rowWrites len) s.mem t.mem) :
    RowInput len B p iv T st t := by
  have hn := hb.nowrap
  have hf := hb.fits16
  have e48 : signSlot = 48 := rfl
  have e16 : win = 16 := rfl
  have r0 := rv_a len 0; have r2 := rv_a len 2; have r4 := rv_a len 4; have r5 := rv_a len 5
  have r6 := rv_a len 6; have r7 := rv_a len 7; have r11 := rv_a len 11
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have word (d : Nat) (hd : d + 4 ≤ 48) :
      t.mem.readW (off B d) 32 = s.mem.readW (off B d) 32 :=
    VG.Proof.Weierstrass.X86.Inv.read32_unch O (by
      intro r hr; simp only [rowWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega) (by omega)
  have value (d k : Nat) (lo : rv (kw len) (a 2) ≤ d) (hi : d + 4 * k ≤ rv (kw len) (a 11)) :
      val32 t.mem B d k = val32 s.mem B d k :=
    Outs.val32 O (by
      intro r hr; simp only [rowWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega) (by omega)
  obtain ⟨⟨hD, hU, hV, hQ, hR⟩, hm, hi, hF, hG, hA, hB⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [word _ (by omega)]; exact hD
  · rw [word _ (by omega)]; exact hU
  · rw [word _ (by omega)]; exact hV
  · rw [word _ (by omega)]; exact hQ
  · rw [word _ (by omega)]; exact hR
  · rw [value _ _ (by omega) (by omega)]; exact hm
  · rw [w32, word _ (by omega)]; exact hi
  · rw [value _ _ (by omega) (by omega)]; exact hF
  · rw [value _ _ (by omega) (by omega)]; exact hG
  · rw [value _ _ (by omega) (by omega)]; exact hA
  · rw [value _ _ (by omega) (by omega)]; exact hB

end VG.Proof.Rsa.X86.InvBatchRt
